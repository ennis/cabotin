use crossbeam_channel::{select, Receiver, Sender};
use irc::client::ext::ClientExt;
use irc::client::prelude::*;
use irc::client::IrcClient;
use irc::proto::message::Message;
use itertools::Itertools;
use log::info;
use rand::seq::SliceRandom;
use std::cmp::max;
use std::cmp::min;
use std::cmp::Ordering;
use std::collections::HashSet;
use std::fmt;
use std::fmt::Write;
use std::thread;
use std::thread::JoinHandle;
use std::time::Duration;
use std::cell::Cell;
use std::collections::HashMap;
use std::sync::Mutex;
use std::sync::Arc;
use std::fs;
use serde::{Serialize,Deserialize};

macro_rules! send_privmsg {
    ($client:expr, $chan:expr, $($arg:tt)*) => ($client.send_privmsg(&$chan, format!($($arg)*)))
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Hand {
    value: u32,
    details: HandDetails,
    cards: [Card; 5],
}

impl Hand
{
    pub fn total_value(&self) -> u32 {
        self.details as u32 + self.value
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct CardSeq<'a>(&'a [Card]);

impl<'a> fmt::Display for CardSeq<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        for (_i, c) in self.0.iter().enumerate() {
            let c = format!("{}", c);
            write!(f, "{: <4}", c)?;
        }
        Ok(())
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum HandDetails {
    // hand value btw. 0 and 9999
    // 80000 + hand value
    StraightFlush = 80000,
    // 70000 + hand value
    FourOfAKind = 70000,
    // 60000 + hand value
    FullHouse = 60000,
    // 50000 + hand value
    Flush = 50000,
    // 40000 + hand value
    Straight = 40000,
    // 30000 + hand value
    ThreeOfAKind = 30000,
    // 20000 + hand value
    TwoPairs = 20000,
    // 10000 + hand value
    Pair = 10000,
    // 0 + hand value
    HighCard = 0,
}

/// Get the best hand of five cards in the specified set
fn get_best_hand(cards: &[Card]) -> Hand {
    // sort by descending rank
    let sorted_by_rank = {
        let mut v = cards.to_vec();
        v.sort_by(|a, b| b.rank.cmp(&a.rank));
        v
    };

    // straights
    let straights = sorted_by_rank
        .as_slice()
        .windows(5)
        .filter(|&w| {
            w[0].rank.value() == w[1].rank.value() + 1
                && w[1].rank.value() == w[2].rank.value() + 1
                && w[2].rank.value() == w[3].rank.value() + 1
                && w[3].rank.value() == w[4].rank.value() + 1
        })
        .enumerate();

    let mut best_straight = None;

    for (_i, w) in straights {
        // first straight in iterator is the best
        if best_straight.is_none() {
            best_straight = Some(w);
        }
        // but the following may be straight flushes
        if w.iter().tuple_windows().all(|(a, b)| a.suit == b.suit) {
            // Straight flush
            return Hand {
                value: w[0].rank.0 as u32,
                details: HandDetails::StraightFlush,
                cards: [w[0], w[1], w[2], w[3], w[4]],
            };
        }
    }

    // create rank runs
    let runs: Vec<Vec<_>> = sorted_by_rank
        .iter()
        .group_by(|c| c.rank)
        .into_iter()
        .map(|(_rank, run)| run.collect::<Vec<_>>())
        .collect();

    // four of a kind
    if let Some(run) = runs.iter().filter(|&run| run.len() == 4).next() {
        let rank = run[0].rank;
        let kicker = sorted_by_rank
            .iter()
            .filter(|c| c.rank != rank)
            .next()
            .unwrap();
        return Hand {
            value: rank.value(),
            details: HandDetails::FourOfAKind,
            cards: [*run[0], *run[1], *run[2], *run[3], *kicker],
        };
    }

    let three_of_a_kind = runs.iter().filter(|&run| run.len() == 3).next();
    let pairs: Vec<_> = runs.iter().filter(|run| run.len() == 2).take(2).collect();
    let num_pairs = pairs.len();

    let sorted_by_suit = {
        let mut v = sorted_by_rank.clone();
        v.sort_by(|a, b| (a.suit, a.rank).cmp(&(b.suit, b.rank)));
        v
    };

    if three_of_a_kind.is_some() && num_pairs > 0 {
        // full house
        let run = three_of_a_kind.unwrap();
        let pair_run = pairs[0];
        Hand {
            value: 100 * run[0].rank.value() + pair_run[0].rank.value(),
            details: HandDetails::FullHouse,
            cards: [*run[0], *run[1], *run[2], *pair_run[0], *pair_run[1]],
        }
    } else if let Some(run) = sorted_by_suit
        .iter()
        .group_by(|c| c.suit)
        .into_iter()
        .map(|(_suit, run)| run.collect::<Vec<_>>())
        .filter(|run| run.len() >= 5)
        .next()
    {
        // flush (note: rank in ascending order)
        Hand {
            value: run[4].rank.value(),
            details: HandDetails::Flush,
            cards: [*run[4], *run[3], *run[2], *run[1], *run[0]],
        }
    } else if let Some(w) = best_straight {
        // straight
        Hand {
            value: w[0].rank.value(),
            details: HandDetails::Straight,
            cards: [w[0], w[1], w[2], w[3], w[4]],
        }
    } else if let Some(run) = three_of_a_kind {
        // three of a kind
        let rank = run[0].rank;
        let mut kickers = sorted_by_rank.iter().filter(|c| c.rank != rank);
        let k0 = kickers.next().unwrap();
        let k1 = kickers.next().unwrap();
        Hand {
            value: 100 * rank.value() + k0.rank.value() + k1.rank.value(),
            details: HandDetails::ThreeOfAKind,
            cards: [*run[0], *run[1], *run[2], *k0, *k1],
        }
    } else if num_pairs == 2 {
        // Two pairs
        let pair1 = pairs[0];
        let rank1 = pair1[0].rank;
        let pair2 = pairs[1];
        let rank2 = pair2[0].rank;
        let kicker = sorted_by_rank
            .iter()
            .filter(|c| c.rank != rank1 && c.rank != rank2)
            .next()
            .unwrap();
        Hand {
            value: 100 * (rank1.value() + rank2.value()) + kicker.rank.value(),
            details: HandDetails::TwoPairs,
            cards: [*pair1[0], *pair1[1], *pair2[0], *pair2[1], *kicker],
        }
    } else if num_pairs == 1 {
        // One pair
        let pair = pairs[0];
        let rank = pair[0].rank;
        let mut kickers = sorted_by_rank.iter().filter(|c| c.rank != rank);
        let k0 = kickers.next().unwrap();
        let k1 = kickers.next().unwrap();
        let k2 = kickers.next().unwrap();
        Hand {
            value: 100 * rank.value() + k0.rank.value() + k1.rank.value() + k2.rank.value(),
            details: HandDetails::Pair,
            cards: [*pair[0], *pair[1], *k0, *k1, *k2],
        }
    } else {
        // High card (nothing)
        Hand {
            value: sorted_by_rank.iter().map(|c| c.rank.value()).sum(),
            details: HandDetails::HighCard,
            cards: [
                sorted_by_rank[0],
                sorted_by_rank[1],
                sorted_by_rank[2],
                sorted_by_rank[3],
                sorted_by_rank[4],
            ],
        }
    }
}

/// Ord is arbitrary here
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Suit {
    Clubs,
    Diamonds,
    Spades,
    Hearts,
}

impl fmt::Display for Suit {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Suit::Clubs => f.write_char('♧'),
            Suit::Diamonds => f.write_char('♢'),
            Suit::Spades => f.write_char('♤'),
            Suit::Hearts => f.write_char('♡'),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Rank(u8); // 2-14(A)

impl Rank {
    pub fn value(&self) -> u32 {
        self.0 as u32
    }
}

impl Rank {
    const JACK: Rank = Rank(11);
    const QUEEN: Rank = Rank(12);
    const KING: Rank = Rank(13);
    const ACE: Rank = Rank(14);
}

impl fmt::Display for Rank {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        match self {
            Rank(r @ 2..=10) => write!(f, "{}", r),
            Rank(11) => write!(f, "J"),
            Rank(12) => write!(f, "Q"),
            Rank(13) => write!(f, "K"),
            Rank(14) => write!(f, "A"),
            _ => panic!(),
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct Card {
    suit: Suit,
    rank: Rank,
}

impl Card {
    pub fn parse(desc: &str) -> Option<Card> {
        let mut chars = desc.chars();
        let suit = match chars.next()? {
            'H' => Suit::Hearts,
            'C' => Suit::Clubs,
            'S' => Suit::Spades,
            'D' => Suit::Diamonds,
            '♡' => Suit::Hearts,
            '♧' => Suit::Clubs,
            '♤' => Suit::Spades,
            '♢' => Suit::Diamonds,
            _ => return None,
        };

        let ch2 = chars.next()?;
        let ch3 = chars.next();

        let rank = match (ch2, ch3) {
            ('J', None) => Rank::JACK,
            ('Q', None) => Rank::QUEEN,
            ('K', None) => Rank::KING,
            ('A', None) | ('1', None) => Rank::ACE,
            ('1', Some('0')) => Rank(10),
            ('9', None) => Rank(9),
            ('8', None) => Rank(8),
            ('7', None) => Rank(7),
            ('6', None) => Rank(6),
            ('5', None) => Rank(5),
            ('4', None) => Rank(4),
            ('3', None) => Rank(3),
            ('2', None) => Rank(2),
            _ => return None,
        };

        Some(Card { suit, rank })
    }
}

impl fmt::Display for Card {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}{}", self.rank, self.suit)
    }
}

#[derive(Clone, Debug)]
pub struct Player {
    name: String,
    chips: Cell<u32>,
}

impl Player {
    /*pub fn take(&mut self, amount: u32) -> Option<u32> {
        if self.chips.get() >= amount {
            self.chips -= amount;
            Some(amount)
        } else {
            None
        }
    }*/
}

pub struct Table {
    players: Vec<Player>,
    //dealer: usize,
}

impl Table {
    /*fn count_live_players(&self) -> usize {
        self.players.iter().filter(|p| p.chips > 0).count()
    }*/

    /*fn next_live_player(&self, from: usize) -> usize {
        let np = self.players.len();
        let mut n = from;
        loop {
            n = (n + 1) % np;
            if self.players[n].chips != 0 {
                break;
            }
        }
        n
    }*/
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum BetState {
    /// Player went all-in
    AllIn,
    /// Player checked
    Check,
    /// Player folded
    Fold,
    /// Player made a bet
    Bet,
}

#[derive(Clone, Debug)]
pub struct LivePlayer<'a> {
    info: &'a Player,
    state: Cell<BetState>,
    bet: Cell<u32>,
    index: usize,
    pocket: (Card,Card)
}

impl<'a> LivePlayer<'a>
{
    pub fn is_allin(&self) -> bool {
        self.state.get() == BetState::AllIn
    }
    pub fn is_fold(&self) -> bool {
        self.state.get() == BetState::Fold
    }
    pub fn is_check(&self) -> bool {
        self.state.get() == BetState::Check
    }
    pub fn best_hand(&self, common: &[Card]) -> Hand {
        let mut all_cards = common.to_vec();
        all_cards.push(self.pocket.0);
        all_cards.push(self.pocket.1);
        get_best_hand(&all_cards)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum BetOutcome<'a, 'tab> {
    NextPlayer(&'a LivePlayer<'tab>),
    AllCheck,
    AllAllIn,
    Win(&'a LivePlayer<'tab>),
}

impl<'a, 'tab> BetOutcome<'a, 'tab> {
    pub fn next_player(&self) -> Option<&'a LivePlayer<'tab>> {
        match self {
            BetOutcome::NextPlayer(p) => Some(p),
            _ => None,
        }
    }

    pub fn is_win(&self) -> bool {
        match self {
            BetOutcome::Win(_) => true,
            _ => false,
        }
    }

    pub fn is_all_allin(&self) -> bool {
        match self {
            BetOutcome::AllAllIn => true,
            _ => false
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum BetError {
    InvalidRaise,
    InvalidPlayer,
    InvalidBet,
    InvalidCheck,
    //NotEnoughChips,
}

type BetResult<'a, 'tab> = Result<BetOutcome<'a, 'tab>, BetError>;

#[derive(Copy, Clone, Debug)]
pub struct Pot {
    bet: u32,
    amount: u32,
}

pub struct Bets<'tab> {
    /// Players
    table: &'tab Table,
    players: Vec<LivePlayer<'tab>>,
    min_start_bet: Cell<u32>,
    bet_to_match: Cell<u32>,
    min_raise: Cell<u32>,
}

impl<'tab> Bets<'tab> {
    pub fn player_by_name(&self, name: &str) -> Option<&LivePlayer> {
        for (i, p) in self.players.iter().enumerate() {
            if p.info.name == name {
                return Some(p);
            }
        }
        None
    }

    fn restart<'a>(&'a self, next: &'a LivePlayer<'tab>) -> BetOutcome<'a,'tab> {
        // reset states
        for p in self.players.iter() {
            match p.state.get() {
                BetState::Bet | BetState::Check => {
                    p.state.set(BetState::Bet);
                }
                _ => {}
            }
        }

        // skip allin & fold players
        let mut p = next;
        loop {
            match p.state.get() {
                BetState::Fold | BetState::AllIn => {
                    p = &self.players[(p.index + 1) % self.players.len()];
                    continue;
                }
                _ => {
                    break;
                }
            }
        }
        BetOutcome::NextPlayer(p)
    }

    pub fn player_by_index(&self, index: usize) -> &LivePlayer<'tab> {
        &self.players[index]
    }

    pub fn new(table: &'tab Table, shuffled_deck: &mut Vec<Card>, dealer: usize) -> (Bets<'tab>, usize) {
        // find the dealer
        let next_dealer = table
            .players
            .iter()
            .enumerate().find(|(i,p)| p.chips.get() != 0 && *i >= dealer).map(|(i,_)| i).unwrap_or(0);

        let mut ii = 0;
        let mut dealer = 0;

        let players: Vec<_> = table
            .players
            .iter()
            .enumerate()
            .filter_map(|(i, p)| {
                if p.chips.get() != 0 {
                    // normally you don't deal cards like that, but it's OK because
                    // they are independent events™
                    let pocket_1 = shuffled_deck.pop().unwrap();
                    let pocket_2 = shuffled_deck.pop().unwrap();
                    // ugly
                    if i == next_dealer {
                        dealer = ii;
                    }
                    ii += 1;
                    Some(LivePlayer {
                        bet: Cell::new(0),
                        state: Cell::new(BetState::Bet),
                        index: i,
                        info: p,
                        pocket: (pocket_1, pocket_2)
                    })
                } else {
                    None
                }
            })
            .collect();

        (Bets {
            table,
            players,
            min_start_bet: Cell::new(1),
            bet_to_match: Cell::new(0),
            min_raise: Cell::new(1),
        }, dealer)
    }

    fn can_check(&self, p: &LivePlayer<'tab>) -> bool {
        assert!(p.bet.get() <= self.bet_to_match.get());
        p.bet.get() == self.bet_to_match.get()
    }

    /// Bet
    /// If betting more than a player has, automatically go all-in
    fn bet<'a>(&'a self, p: &LivePlayer<'tab>, bet: u32) -> BetResult<'a,'tab> {
        // allin players don't do anything
        if p.is_fold() || p.is_allin() {
            return Err(BetError::InvalidPlayer);
        }

        // bet == 0 is check
        if bet == 0 {
            // can't check, needs to call, fold or raise
            if p.bet.get() < self.bet_to_match.get() {
                return Err(BetError::InvalidCheck);
            } else {
                // OK check
                p.state.set(BetState::Check);
                return Ok(self.calculate_outcome(p));
            }
        }

        // Can't bet below...
        if bet <= p.bet.get() {
            return Err(BetError::InvalidBet);
        }

        // check chips, adjust bet
        let all_in = p.info.chips.get() <= (bet - p.bet.get());
        let bet = p.bet.get() + min(p.info.chips.get(), bet - p.bet.get());

        // check bet
        // can still go all in if not enough
        if !all_in && (bet < self.min_start_bet.get() || bet < self.bet_to_match.get()) {
            return Err(BetError::InvalidBet);
        }

        // All OK on player side
        // handle raise
        // note that all-ins bypass this rule
        let raised = bet > self.bet_to_match.get();
        if raised {
            if !all_in && (bet - self.bet_to_match.get() < self.min_raise.get()) {
                return Err(BetError::InvalidRaise);
            }
            // OK raise
            // update min raise
            self.min_raise.set(bet - self.bet_to_match.get());
            self.bet_to_match.set(bet);
        }

        // commit
        let diff = bet - p.bet.get();
        p.bet.set(bet);
        p.info.chips.set(p.info.chips.get() - diff);

        if all_in {
            p.state.set(BetState::AllIn);
        } else {
            p.state.set(BetState::Bet);
        }

        Ok(self.calculate_outcome(p))
    }

    /// Player calls the max bet
    fn call<'a>(&'a self, p: &LivePlayer<'tab>) -> BetResult<'a,'tab> {
        // player places a bet, or a raise (checked upstream)
        // if player has not enough, then he goes all-in
        self.bet(p, self.bet_to_match.get())
    }

    /// Player raises
    fn raise<'a>(&'a self, p: &LivePlayer<'tab>, raise_by: u32) -> BetResult<'a,'tab> {
        self.bet(p, self.bet_to_match.get() + raise_by)
    }

    /// Player checks
    fn check<'a>(&'a self, p: &LivePlayer<'tab>) -> BetResult<'a,'tab> {
        self.bet(p, 0)
    }

    /// Player goes all-in
    fn all_in<'a>(&'a self, p: &LivePlayer<'tab>) -> BetResult<'a,'tab> {
        let chips = p.info.chips.get();
        let bet = p.bet.get();
        self.bet(p, bet + chips)
    }

    /// Player folds
    fn fold<'a>(&'a self, p: &LivePlayer<'tab>) -> BetResult<'a,'tab> {
        p.state.set(BetState::Fold);
        Ok(self.calculate_outcome(p))
    }

    /// Calculate the next action to do after a player's turn
    fn calculate_outcome<'a>(&'a self, p: &LivePlayer<'tab>) -> BetOutcome<'a, 'tab> {
        let pi = p.index;
        let mut num_live = 0;
        let mut next = None; // next to play (may not be live if allin)
        let mut live = None; // potential winner
        let mut all_allin = true;
        let mut player_iter = self.players.iter().enumerate().cycle().skip(pi + 1);

        // all players starting from the next one
        loop {
            let (i, p) = player_iter.next().unwrap();
            //assert!(p.bet.get() <= self.bet_to_match.get());

            if p.state.get() != BetState::Fold {
                num_live += 1;
                if live.is_none() {
                    live = Some(p);
                }
            }

            match p.state.get() {
                BetState::Check => {
                    if p.bet.get() != self.bet_to_match.get() {
                        // checked, but someone raised: must play next
                        if next.is_none() {
                            next = Some(p);
                        }
                    }
                    all_allin = false;
                }
                BetState::Bet => {
                    if next.is_none() {
                        next = Some(p);
                    }
                    all_allin = false;
                }
                BetState::AllIn | BetState::Fold => {}
            }

            // went through the whole table
            if i == pi {
                break;
            }
        }

        if num_live == 1 {
            BetOutcome::Win(live.unwrap())
        } else {
            if let Some(next) = next {
                BetOutcome::NextPlayer(next)
            } else if all_allin {
                BetOutcome::AllAllIn
            } else {
                BetOutcome::AllCheck
            }
        }
    }

    /// Total amount of chips in the pot
    fn pot_total(&self) -> u32 {
        self.players.iter().map(|p| p.bet.get()).sum()
    }

    /// Calculate the side pots
    fn calculate_side_pots(&self) -> Vec<Pot> {
        let pot_total = self.pot_total();

        let mut allins: Vec<_> = self
            .players
            .iter()
            .filter(|p| p.is_allin())
            .collect();
        // sort by bet
        allins.sort_by(|a, b| a.bet.get().cmp(&b.bet.get()));

        let mut side_pots = Vec::new();
        side_pots.push(Pot {
            bet: self.bet_to_match.get(),
            amount: pot_total,
        });

        let mut m = 0;
        for a in allins {
            // take the difference to the bet of each player and place it in a side pot
            let extra = a.bet.get() - m;
            m = a.bet.get();
            let side = self.players.iter().map(|p| max(p.bet.get() - extra, 0)).sum();
            // no side pot, this is the biggest bet yet
            if side == 0 {
                break;
            }
            side_pots.last_mut().unwrap().amount -= side;
            side_pots.push(Pot {
                bet: a.bet.get(),
                amount: side,
            });
        }

        dbg!(side_pots)
    }
}

fn play_betting_round<'a, 'tab>(
    bets: &'a Bets<'tab>,
    next: &'a LivePlayer<'tab>,
    client: &IrcClient,
    common: &[Card],
    chan: &str,
    inputs: &Receiver<UserMsg>,
) -> BetOutcome<'a, 'tab>
{
    let mut p = bets.restart(next).next_player().unwrap();

    'player: loop {
        let p_name = p.info.name.clone();
        send_privmsg!(
            client,
            chan,
            "Joueur {}, c'est à vous (votre mise: {}, à atteindre: {}) (!call, !raise, !check, !fold, !quit, !see, !pot)",
            p_name,
            p.bet.get(),
            bets.bet_to_match.get(),
        );
        // repeat until valid action
        'action: loop {
            let action = recv_action(client, chan, &p_name, inputs);
            let result = match action {
                Action::ShowChips(p_name) => {
                    if let Some(p) = bets.player_by_name(&p_name) {
                        send_privmsg!(
                            client,
                            chan,
                            "{}_, vos chips: {} (misés: {})",
                            p_name,
                            p.info.chips.get(),
                            p.bet.get()
                        );
                    }
                    continue;
                }
                Action::ShowBets => {
                    for p in bets.players.iter() {
                        let checked = p.is_check();
                        let allin = p.is_allin();
                        let fold = p.is_fold();
                        send_privmsg!(
                            client,
                            chan,
                            "{}_ mise {} chips {}{}{} (restants: {})",
                            p.info.name,
                            p.bet.get(),
                            if checked { "(checked)" } else { "" },
                            if allin { "(tapis)" } else { "" },
                            if fold { "(couché)" } else { "" },
                            p.info.chips.get(),
                        );
                    }
                    continue;
                }
                Action::SeeCards(p_name) => {
                    if let Some(p) = bets.player_by_name(&p_name) {
                        send_privmsg!(client, p_name, "Vos cartes: {}, {}", p.pocket.0, p.pocket.1);
                        if common.len() >= 3 {
                            let best = p.best_hand(common);
                            send_privmsg!(
                                client,
                                p_name,
                                "Meilleure main: {} ({:?})",
                                CardSeq(&best.cards),
                                best.details
                            );
                        }
                    }
                    continue;
                }
                Action::AllIn => bets.all_in(p),
                Action::Raise(by) => bets.raise(p, by),
                Action::Check => bets.check(p),
                Action::Fold => bets.fold(p),
                Action::Bet(amount) => bets.bet(p, amount),
                Action::Call => bets.call(p),
                Action::Quit => unimplemented!(),
                Action::None => {
                    continue 'action;
                }
            };

            info!("player {} turn finished, outcome is {:?}", p_name, result);

            let outcome = match result {
                Ok(outcome) => {
                    match p.state.get() {
                        BetState::Check => {
                            send_privmsg!(
                                client,
                                chan,
                                "{}_ check! (à misé {})",
                                p_name,
                                p.bet.get()
                            );
                        },
                        BetState::Fold => {
                            send_privmsg!(
                                client,
                                chan,
                                "{}_ se couche... (et laisse {} chips)",
                                p_name,
                                p.bet.get()
                            );
                        },
                        BetState::AllIn => {
                            send_privmsg!(
                                client,
                                chan,
                                "{}_ fait tapis! (et mise {} chips)",
                                p_name,
                                p.bet.get()
                            );
                        }
                        _ => {
                            send_privmsg!(
                                client,
                                chan,
                                "{}_ mise {} chips",
                                p_name,
                                p.bet.get()
                            );
                        }
                    }
                    outcome
                }
                Err(e) => match e {
                    BetError::InvalidBet => {
                        send_privmsg!(client, chan, "Pari non valide");
                        continue 'action;
                    }
                    BetError::InvalidCheck => {
                        send_privmsg!(client, chan, "Vous ne pouvez pas !check: votre mise est de {}, la mise à atteindre est de {}. !call pour miser {}, !raise <combien> pour surencherir, !fold pour se coucher",
                            p.bet.get(),
                            bets.bet_to_match.get(),
                            bets.bet_to_match.get());
                        continue 'action;
                    }
                    BetError::InvalidRaise => {
                        send_privmsg!(
                            client,
                            chan,
                            "Le montant minimum d'une surenchère est de {}",
                            bets.min_raise.get()
                        );
                        continue 'action;
                    }
                    _ => panic!(),
                },
            };

            match outcome {
                BetOutcome::Win(win) => {
                    let pot = bets.pot_total();
                    // TODO handle side pots
                    send_privmsg!(client, chan, "** {} rafle la mise... ({} chips)", win.info.name, pot);
                    win.info.chips.set(win.info.chips.get() + pot);
                    return outcome;
                }
                BetOutcome::AllCheck | BetOutcome::AllAllIn => return outcome,
                BetOutcome::NextPlayer(next) => p = next,
            }

            break;
        }
    }

}

enum Action {
    None,
    Check,
    AllIn,
    Bet(u32),
    Raise(u32),
    Call,
    Fold,
    Quit,
    ShowBets,
    ShowChips(String),
    SeeCards(String),
}

struct PlayConfig {
    init_small_blind: u32,
    init_big_blind: u32,
}

struct UserMsg {
    chan: String,
    nick: String,
    msg: String,
}

fn parse_amount(s: &str) -> Option<u32> {
    s.find(' ')
        .and_then(|n| s.split_at(n).1.trim().parse::<u32>().ok())
}

fn recv_action(client: &IrcClient, chan: &str, player: &str, inputs: &Receiver<UserMsg>) -> Action {
    loop {
        let m = inputs.recv().unwrap();
        if m.chan != chan {
            continue;
        }

        let s = m.msg.as_str();
        if s.starts_with("!bet") {
            if m.nick != player {
                continue;
            }
            if let Some(bet) = parse_amount(s) {
                break Action::Bet(bet);
            } else {
                send_privmsg!(client, chan, "Combien? (!bet <combien>)");
            }
        } else if s.starts_with("!allin") {
            if m.nick != player {
                continue;
            }
            break Action::AllIn;
        } else if s.starts_with("!see") {
            break Action::SeeCards(m.nick);
        } else if s.starts_with("!check") {
            if m.nick != player {
                continue;
            }
            break Action::Check;
        } else if s.starts_with("!raise") {
            if m.nick != player {
                continue;
            }
            if let Some(bet) = parse_amount(s) {
                break Action::Raise(bet);
            } else {
                send_privmsg!(client, chan, "Combien? (!raise <combien>)");
            }
        } else if s.starts_with("!fold") {
            if m.nick != player {
                continue;
            }
            break Action::Fold;
        } else if s.starts_with("!call") {
            if m.nick != player {
                continue;
            }
            break Action::Call;
        } else if s.starts_with("!quit") {
            if m.nick != player {
                continue;
            }
            break Action::Quit;
        } else if s.starts_with("!pot") {
            break Action::ShowBets;
        } else if s.starts_with("!chips") {
            break Action::ShowChips(m.nick);
        }
    }
}

fn play_poker(client: IrcClient, inputs: Receiver<UserMsg>, state: Arc<Mutex<PokerState>>) {
    use crossbeam_channel::after;

    send_privmsg!(client, "#contreloutre", "re");

    loop {
        // wait for someone to say !poker
        let mut players = HashSet::new();

        let UserMsg {
            nick: first_player,
            chan,
            msg,
        } = inputs.recv().unwrap();

        if msg != "!poker" {
            continue;
        }

        let entry = 100;

        send_privmsg!(client, chan, "Texas Hold'em: !poker pour jouer, entrée à {} chips", entry);
        players.insert(first_player);

        // wait for players
        let timeout = after(Duration::from_secs(60));
        loop {
            select! {
                recv(inputs) -> usermsg => {
                    let usermsg = usermsg.unwrap();
                    if usermsg.msg == "!poker" {
                        // check enough chips
                        let mut s = state.lock().unwrap();
                        if s.chips.get(&usermsg.nick).unwrap_or(&0) <= &entry {
                            send_privmsg!(client, chan, "T'as pas assez de chips, {}", usermsg.nick);
                        }

                        info!("{} in the game", usermsg.nick);
                        players.insert(usermsg.nick);
                    }
                }
                recv(timeout) -> _ => {
                    info!("timeout. players {:?}", players);
                    break
                },
            };
        }

        let num_players = players.len();
        if num_players < 2 {
            send_privmsg!(client, chan, "Pas assez de joueurs");
            continue;
        }

        let cfg = PlayConfig {
            init_small_blind: 2,
            init_big_blind: 5,
        };

        send_privmsg!(client, chan, "Joueurs: {}", players.iter().join(","));
        send_privmsg!(
            client,
            chan,
            "Petite blinde: {} chips, grosse blinde: {} chips, entrée à {} chips",
            cfg.init_small_blind,
            cfg.init_big_blind,
            100
        );

        let players: Vec<_> = players
            .into_iter()
            .map(|name| Player {
                name,
                chips: Cell::new(100), // TODO
            })
            .collect();

        let table = Table { players };

        // initial dealer is first player
        let mut dealer = 0;

        // deals
        'game: loop {
            // deal cards to all live players
            let mut deck = create_shuffled_deck();
            let (mut bets, dealer) = Bets::new(&table, &mut deck, dealer);

            let num_live_players = bets.players.len();
            if num_live_players < 2 {
                break 'game;
            }

            let dealer = bets.player_by_index(dealer);

            // show cards to all players
            for p in bets.players.iter() {
                send_privmsg!(client, p.info.name, "** Vos cartes: {}, {}", p.pocket.0, p.pocket.1);
            }

            let next = if num_live_players == 2 {
                // 1. small blind (dealer)
                let next = bets.bet(dealer, cfg.init_small_blind).unwrap().next_player().unwrap();
                // 2. big blind
                let next = bets.bet(next, cfg.init_big_blind).unwrap().next_player().unwrap();
                next
            } else {
                // skip dealer
                // the dealer does not really check but it's functionally equivalent (i hope)
                let next = bets.check(dealer).unwrap().next_player().unwrap();
                // 1. small blind
                let next = bets.bet(next, cfg.init_small_blind).unwrap().next_player().unwrap();
                // 2. big blind
                let next = bets.bet(next, cfg.init_big_blind).unwrap().next_player().unwrap();
                next
            };

            // show thunes
            send_privmsg!(client, chan, "=== CHIPS: ===");
            for p in bets.players.iter() {
                let mut msg = format!("{}: {} chips", p.info.name, p.info.chips.get());
                let bet = p.bet.get();
                if bet == cfg.init_small_blind {
                    write!(msg, ", mise {} (petite blinde)", bet);
                }
                else if bet == cfg.init_big_blind {
                    write!(msg, ", mise {} (grosse blinde)", bet);
                }

                send_privmsg!(client, chan, "{}", msg);
            }

            // pre-flop betting round
            let mut outcome =
                play_betting_round(&bets, next, &client, &[], &chan, &inputs);
            if outcome.is_win() {
                continue;
            }

            let show_best_hands = |common: &[Card], bets: &Bets| {
                for p in bets.players.iter() {
                    let best = p.best_hand(&common);
                    let p_name = &p.info.name;
                    send_privmsg!(
                        client,
                        p_name,
                        "Meilleure main: {} ({:?})",
                        CardSeq(&best.cards),
                        best.details
                    );
                }
            };

            // draw flop
            let mut community = Vec::new();
            community.push(deck.pop().unwrap());
            community.push(deck.pop().unwrap());
            community.push(deck.pop().unwrap());
            send_privmsg!(client, chan, "** FLOP: {}", CardSeq(&community));
            show_best_hands(&community, &bets);

            // 2nd betting round
            if !outcome.is_all_allin() {
                outcome = play_betting_round(
                    &bets, next, &client, &community, &chan, &inputs,
                );
                if outcome.is_win() {
                    continue;
                }
            }

            // draw turn
            community.push(deck.pop().unwrap());
            send_privmsg!(client, chan, "** TURN: {}", CardSeq(&community));
            show_best_hands(&community, &bets);

            // 3rd betting round
            if !outcome.is_all_allin() {
                outcome = play_betting_round(
                    &bets, next, &client, &community, &chan, &inputs,
                );
                if outcome.is_win() {
                    continue;
                }
            }

            // river
            community.push(deck.pop().unwrap());
            send_privmsg!(client, chan, "** RIVER: {}", CardSeq(&community));
            show_best_hands(&community, &bets);

            // final betting round
            if !outcome.is_all_allin() {
                outcome = play_betting_round(
                    &bets, next, &client, &community, &chan, &inputs,
                );
                if outcome.is_win() {
                    continue;
                }
            }

            send_privmsg!(client, chan, "¡¡SHOWTIME!!");

            // showdown
            let mut players : Vec<_> = bets.players.iter().map(|p| (p, p.best_hand(&community))).collect();
            players.sort_by(|a,b| b.1.total_value().cmp(&a.1.total_value()));

            let winner = &players[0];
            let pot = bets.pot_total();
            // TODO handle side pots
            send_privmsg!(client, chan,
                "** {} : {} ({:?}) | GAGNANT! ({} chips)",
                    winner.0.info.name,
                    CardSeq(&winner.1.cards),
                    winner.1.details,
                    pot
                );
            winner.0.info.chips.set(winner.0.info.chips.get() + pot);

            for p in players[1..].iter() {
                send_privmsg!(client, chan,
                    "** {} : {} ({:?})",
                    p.0.info.name,
                    CardSeq(&p.1.cards),
                    p.1.details,
                    );
            }
        }

        send_privmsg!(client, chan, "Fin de la partie. Chips:");
        for p in table.players.iter() {
            send_privmsg!(client, chan, "{}_: {} chips", p.name, p.chips.get());
        }
    }
}

#[derive(Serialize, Deserialize)]
struct PokerState {
    chips: HashMap<String, u32>,
}

impl PokerState
{
    fn load() -> PokerState {
        toml::from_str(&fs::read_to_string("chips.toml").expect("could not open chips")).unwrap()
    }

    fn save(&self) {
        fs::write("chips.toml", toml::to_string(self).unwrap()).expect("could not save chips")
    }

    fn transaction(&mut self, nick: &str, diff: i32) -> bool {
        let v = self.chips.entry(nick.to_string()).or_insert(0);

        // meh...
        match diff {
            d if d < 0 => {
                let s = (-d) as u32;
                if *v < s {
                    return false;
                }
                *v -= s as u32;
            }
            d => {
                *v += d as u32;
            }
        }
        true
    }

    fn show_all(&self, client: &IrcClient, chan: &str) {
        for (k,v) in self.chips.iter() {
            send_privmsg!(client, chan, "{}_: {} chips", k, v);
        }
    }

    fn show_one(&self, client: &IrcClient, chan: &str, nick: &str) {
        let v = self.chips.get(nick).unwrap_or(&0);
        send_privmsg!(client, chan, "{}_: {} chips", nick, v);
    }
}

pub struct PokerClient {
    client: IrcClient,
    join_handle: JoinHandle<()>,
    tx: Sender<UserMsg>,
    chips: Arc<Mutex<PokerState>>,
    next_recipient: Option<String>,
}

impl PokerClient {
    fn start(client: IrcClient) -> PokerClient {
        let (tx, rx) = crossbeam_channel::unbounded();
        let chips = Arc::new(Mutex::new(PokerState::load()));
        let chips2 = chips.clone();
        let client2 = client.clone();
        let join_handle = thread::spawn(move || {
            play_poker(client2, rx, chips2);
        });
        // load from toml
        PokerClient { client, join_handle, tx, chips, next_recipient: None }
    }

    fn handle_transaction(&mut self, from: &str, msg: &str)
    {
        let msg = msg.trim();
        if msg == "!buy chips" {
            info!("transaction: next recipient is {}", from);
            self.next_recipient = from.to_owned().into();
            return;
        }

        if from == "mklutra" {
            if msg.starts_with("Ca fera ") && msg.ends_with(" chips") {
                if let Some(next) = self.next_recipient.take() {
                    let amount_str = msg.split_at(8).1.split(' ').next().unwrap();
                    let a = amount_str.parse::<i32>().ok();
                    let a = if let Some(a) = a { a } else {
                        info!("transaction: could not parse chips ({})", amount_str);
                        return;
                    };
                    info!("transaction: {} receiving {} chips", next, a);
                    let mut state = self.chips.lock().unwrap();
                    state.transaction(&next, a);
                }
            }
        }
    }

    fn handle_message(&mut self, message: &Message) {
        match message.command {
            Command::PRIVMSG(ref target, ref msg) => {
                if let Some(nick) = message.source_nickname() {
                    self.tx.send(UserMsg {
                        nick: nick.to_string(),
                        chan: target.to_string(),
                        msg: msg.to_string(),
                    });
                    self.handle_transaction(nick, msg);
                    // handle !chips & !chipsall
                    if msg.starts_with("!chipsall") {
                        send_privmsg!(self.client, target, "On va manger... des CHIPS");
                        self.chips.lock().unwrap().show_all(&self.client, target);
                    }
                    else if msg.starts_with("!chips") {
                        self.chips.lock().unwrap().show_one(&self.client, target, nick);
                    }
                }
            }
            _ => {}
        }
    }
}

fn main() {
    // We can also load the Config at runtime via Config::load("path/to/config.toml")
    pretty_env_logger::init();
    info!("starting poker");
    let config = Config::load("config.toml").expect("config.toml not found or unreadable");

    let mut reactor = IrcReactor::new().unwrap();
    let client = reactor.prepare_client_and_connect(&config).unwrap();
    client.identify().unwrap();

    let mut poker = PokerClient::start(client.clone());

    reactor.register_client_with_handler(client, move |_client, message| {
        print!("{}", message);
        // fwd to all games
        poker.handle_message(&message);

        Ok(())
    });

    reactor.run().unwrap();
}

fn create_shuffled_deck() -> Vec<Card> {
    let mut deck = Vec::new();
    for &suit in &[Suit::Diamonds, Suit::Spades, Suit::Clubs, Suit::Hearts] {
        for rank in 2..=14 {
            deck.push(Card {
                suit,
                rank: Rank(rank),
            })
        }
    }

    deck.shuffle(&mut rand::thread_rng());
    deck
}

fn deal_random_hand(num_cards: usize) -> Vec<Card> {
    create_shuffled_deck().into_iter().take(num_cards).collect()
}

#[cfg(test)]
mod tests {
    use crate::Table;
    use crate::*;

    fn hand(h: &str) -> Vec<Card> {
        h.split(' ')
            .filter(|s| !s.is_empty())
            .map(Card::parse)
            .map(Option::unwrap)
            .collect()
    }

    fn c(s: &str) -> Card {
        Card::parse(s).unwrap()
    }

    #[test]
    fn hands() {
        let royal = hand("SA SK SQ SJ S10 H2 C2");
        let straight = hand("S10 H2 H8 S7 S6 C9 C2");
        let pair = hand("S10 H2 H8 S7 S6 H4 C4");
        let two_pairs = hand("SK C4 CK S6 H8 S8 H4");

        assert_eq!(
            get_best_hand(&royal),
            Hand {
                value: 14,
                details: HandDetails::StraightFlush,
                cards: [c("SA"), c("SK"), c("SQ"), c("SJ"), c("S10")]
            }
        );

        assert_eq!(
            get_best_hand(&straight),
            Hand {
                value: 10,
                details: HandDetails::Straight,
                cards: [c("S10"), c("C9"), c("H8"), c("S7"), c("S6")]
            }
        );

        assert_eq!(
            get_best_hand(&pair),
            Hand {
                value: 425,
                details: HandDetails::Pair,
                cards: [c("H4"), c("C4"), c("S10"), c("H8"), c("S7")]
            }
        );

        assert_eq!(
            get_best_hand(&two_pairs),
            Hand {
                value: 2106,
                details: HandDetails::TwoPairs,
                cards: [c("SK"), c("CK"), c("H8"), c("S8"), c("S6")]
            }
        );

        for _ in 0..10000 {
            let cards = deal_random_hand(7);
            let hand = get_best_hand(&cards);
            eprintln!(
                "deal: {}, best: {} ({:?}, {})",
                CardSeq(&cards),
                CardSeq(&hand.cards),
                hand.details,
                hand.value
            );
        }

        panic!()
    }

    fn init_table() -> Table {
        let players = vec![
            Player {
                name: "A".to_string(),
                chips: Cell::new(50),
            },
            Player {
                name: "B".to_string(),
                chips: Cell::new(50),
            },
            Player {
                name: "C".to_string(),
                chips: Cell::new(50),
            },
            Player {
                name: "D".to_string(),
                chips: Cell::new(50),
            },
        ];
        Table { players }
    }

    /*#[test]
    fn betting_round() {
        let mut table = init_table();
        let mut bets = Bets::new(&mut table);
        // 1. small blind
        let next = bets.bet(0, 2).unwrap().next_player().unwrap();
        // 2. big blind
        let next = bets.bet(next, 5).unwrap().next_player().unwrap();
        // 3. Fold
        let next = bets.fold(next).unwrap().next_player().unwrap();
        // 4. Raise by 20 to 25
        let next = bets.raise(next, 20).unwrap().next_player().unwrap();
        // 1. Call
        let next = bets.call(next).unwrap().next_player().unwrap();
        // 2. Fold
        let next = bets.fold(next).unwrap().next_player().unwrap();
        // 4. All in
        let next = bets.all_in(next).unwrap().next_player().unwrap();
        // 1. All in
        let next = bets.all_in(next).unwrap();
        assert_eq!(next, BetOutcome::AllCheck);
    }

    #[test]
    fn betting_round_2() {
        let mut table = init_table();
        let mut bets = Bets::new(&mut table);
        // 1. small blind
        let next = bets.bet(0, 2).unwrap().next_player().unwrap();
        // 2. big blind
        let next = bets.bet(next, 5).unwrap().next_player().unwrap();
        // 3. Try check
        assert_eq!(bets.check(next), Err(BetError::InvalidCheck));
        // 3. Call
        let next = bets.call(next).unwrap().next_player().unwrap();
        // 4. Call
        let next = bets.call(next).unwrap().next_player().unwrap();
        // 1. Call
        let next = bets.call(next).unwrap().next_player().unwrap();
        // 2. Try call, invalid
        assert_eq!(bets.call(next), Err(BetError::InvalidBet));
        // 2. Check
        let next = bets.check(next).unwrap().next_player().unwrap();
        // 3. Check
        let next = bets.check(next).unwrap().next_player().unwrap();
        // 4. Check
        let next = bets.check(next).unwrap().next_player().unwrap();
        // 1. Check
        let next = bets.check(next).unwrap();
        assert_eq!(next, BetOutcome::AllCheck);
    }

    #[test]
    fn betting_round_3() {
        let mut table = init_table();
        let mut bets = Bets::new(&mut table);
        // 1. small blind
        let next = bets.bet(0, 2).unwrap().next_player().unwrap();
        // 2. big blind
        let next = bets.bet(next, 5).unwrap().next_player().unwrap();
        // 3. Call
        let next = bets.call(next).unwrap().next_player().unwrap();
        // 4. Call
        let next = bets.call(next).unwrap().next_player().unwrap();
        // 1. Call
        let next = bets.call(next).unwrap().next_player().unwrap();
        // 2. Check
        let next = bets.check(next).unwrap().next_player().unwrap();
        // 3. Check
        let next = bets.check(next).unwrap().next_player().unwrap();
        // 4. Check
        let next = bets.check(next).unwrap().next_player().unwrap();
        // 1. Allin
        let next = bets.all_in(next).unwrap().next_player().unwrap();
        // 2. Fold
        let next = bets.fold(next).unwrap().next_player().unwrap();
        // 3. Fold
        let next = bets.fold(next).unwrap().next_player().unwrap();
        // 4. Fold
        let next = bets.fold(next).unwrap();

        assert_eq!(next, BetOutcome::Win(0));
    }*/
}
