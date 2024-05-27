use crate::algo::*;
use crate::re::{len_utf8};

use rng::chacha20::*;
use rng::dist::{Draw, FastRangeU32};

use std::cell::{RefCell};
use std::cmp::{min};
use std::fmt::{Debug, Formatter, Result as FmtResult};
use std::io::{Seek, SeekFrom};
use std::mem::{replace};
use std::ops::{BitAnd, BitOr, Sub};
use std::panic::{Location};
use std::rc::{Rc};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct SNum(i8);

impl Debug for SNum {
  fn fmt(&self, f: &mut Formatter) -> FmtResult {
    write!(f, "SNum({})", self.0)
  }
}

impl SNum {
  pub fn nil() -> SNum {
    SNum(0)
  }
}

#[derive(Default)]
pub struct CharTrie {
  root: CharTrieNode,
}

impl CharTrie {
  pub fn match_<Q: AsRef<str>>(&self, query: Q) -> Option<(usize, u32)> {
    let mut curp = 0;
    let mut matp = 0;
    let mut matv = u32::max_value();
    self.root.search(query.as_ref(), &mut curp, &mut matp, &mut matv);
    if matv != u32::max_value() {
      Some((matp, matv))
    } else {
      None
    }
  }

  pub fn insert<K: AsRef<str>>(&mut self, key: K, val: u32) {
    assert!(val < u32::max_value());
    self.root.append(key.as_ref(), val);
  }
}

#[derive(Default)]
pub struct CharTrieNode {
  edge: BTreeMap<char, (u32, CharTrieNode)>,
}

impl CharTrieNode {
  pub fn search(&self, query: &str, curp: &mut usize, matp: &mut usize, matv: &mut u32) {
    match query.get(*curp .. ).unwrap().chars().next() {
      None => return,
      Some(c) => {
        let clen = len_utf8(c as _);
        *curp += clen;
        match self.edge.get(&c) {
          None => return,
          Some(&(leaf, ref t)) => {
            if leaf != u32::max_value() {
              *matp = *curp;
              *matv = leaf;
            }
            t.search(query, curp, matp, matv);
          }
        }
      }
    }
  }

  pub fn append(&mut self, key: &str, leaf: u32) {
    match key.chars().next() {
      None => panic!("bug"),
      Some(c) => {
        let clen = len_utf8(c as _);
        if key.len() < clen {
          panic!("bug");
        } else if key.len() == clen {
          self._append(c, None, leaf);
        } else /*if key.len() > clen */{
          self._append(c, Some(key.get(clen .. ).unwrap()), leaf);
        }
      }
    }
  }

  pub fn _append(&mut self, c: char, knt: Option<&str>, leaf: u32) {
    match self.edge.get(&c) {
      None => {
        self.edge.insert(c, (u32::max_value(), CharTrieNode::default()));
      }
      Some(_) => {}
    }
    match self.edge.get_mut(&c) {
      None => panic!("bug"),
      Some(&mut (ref mut leaf_, ref mut t)) => {
        match knt {
          None => {
            let oleaf = *leaf_;
            if oleaf > leaf {
              *leaf_ = leaf;
            }
          }
          Some(key) => {
            t.append(key, leaf);
          }
        }
      }
    }
  }
}

#[derive(Clone)]
pub struct AttrStr {
  pub start: u32,
  pub end: u32,
  // FIXME: SafeStr.
  pub val: SmolStr,
}

impl Debug for AttrStr {
  fn fmt(&self, f: &mut Formatter) -> FmtResult {
    write!(f, "AttrStr({}:{} {:?})", self.start, self.end, safe_ascii(self.val.as_bytes()))
  }
}

impl AttrStr {
  #[inline]
  pub fn as_raw_str(&self) -> &str {
    &self.val
  }

  #[inline]
  pub fn to_praline_str(&self) -> SmolStr {
    // NB: escape unicode like json.
    // FIXME: need latex-aware escape_str.
    let j: rustc_serialize::json::Json = self.val.clone().into();
    let s = format!("{}", j);
    s.get(1 .. s.len() - 1).unwrap().into()
  }

  #[inline]
  pub fn to_praline_attr(&self) -> SmolStr {
    format!("@{}:{}", self.start, self.end).into()
  }
}

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
pub enum NameKind {
  AnonAtom,
  LatexAtom,
  LitAtom,
}

#[derive(Debug)]
pub struct Name {
  pub kind: NameKind,
  // FIXME: attr.
  pub val: SmolStr,
  //pub val: AttrStr,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Name_ {
  LatexSign(SmolStr),
  LatexAtom(Box<[SNum]>),
}

pub type TraceEntryRef = Rc<TraceEntry>;

#[derive(Clone, Debug)]
pub enum TraceEntry {
  Decode(AttrStr),
  Replay(ReplayLogEntry),
  Fresh_(ReplayLogEntry),
  ReduceItem_(ItemNum, ItemKind),
  ReduceItem2(ItemNum, ItemKind, ItemNum, ItemKind),
  Anchor(ItemNum, ItemKind),
  LinkSup_(ItemNum, ItemKind, ItemNum, ItemKind),
  LinkSup2(ItemNum, ItemKind, ItemNum, ItemKind, ItemNum, ItemKind),
  Recompile(ItemNum),
  NodeInit_(ItemNum, ItemKind, bool),
  NodeApply(ItemNum, Option<NodeKind>, ItemNum, Option<NodeKind>),
  RootStop_(ItemNum, ItemNum),
}

pub type UDraw = u16;
//pub type UDraw = u32;

#[derive(Clone, Copy, Debug)]
pub enum ReplayLogEntry {
  Draw{val: UDraw, ub: UDraw, /*label: SmolStr,*/ loc: StaticLoc_},
  DrawRot{val: UDraw, ub: UDraw, rot: UDraw, loc: StaticLoc_},
}

#[derive(Debug)]
pub struct PvCacheEntry {
  pub matp: u32,
  pub btct: i32,
  pub res:  Result<(), Err_>,
  pub buf:  Vec<ReplayLogEntry>,
}

pub struct ReplayLog {
  // TODO
  ctlp: u32,
  comp: u32,
  //chkp: u32,
  pivp: u32,
  fail: bool,
  trace: bool,
  btct: i32,
  btub: i32,
  buf:  Vec<ReplayLogEntry>,
  tracebuf: Vec<TraceEntry>,
  pv_cache: Vec<PvCacheEntry>,
  draw_ptr: FxHashMap<StaticLoc, u32>,
}

impl Default for ReplayLog {
  fn default() -> ReplayLog {
    ReplayLog{
      ctlp: 0,
      comp: 0,
      //chkp: 0,
      pivp: 0,
      fail: false,
      trace: false,
      btct: 0,
      btub: i32::max_value(),
      buf:  Vec::new(),
      tracebuf: Vec::new(),
      pv_cache: Vec::new(),
      draw_ptr: FxHashMap::default(),
    }
  }
}

impl ReplayLog {
  pub fn set_trace(&mut self, flag: bool) {
    // TODO
    self.trace = flag;
  }

  pub fn _reset(&mut self) {
    unimplemented!();
  }

  pub fn rewind(&mut self) {
    self.ctlp = 0;
    self.tracebuf.clear();
    self.draw_ptr.clear();
  }

  pub fn _next_draw(&mut self, ub_: UDraw, loc_: StaticLoc_) -> Result<UDraw, ()> {
    assert!(1 <= ub_);
    if ub_ == 1 {
      return Ok(0);
    }
    if self.fail {
      return Err(());
    }
    loop {
      if self.ctlp < self.comp {
        let entry = self.buf[self.ctlp as usize];
        match entry {
          ReplayLogEntry::Draw{val, ub, ..} => {
            if self.trace {
              //println!("TRACE:  ReplayLog::_next_draw: comp={} ctlp={} v={} ub={} pre   loc={:?}", self.comp, self.ctlp, val, ub, loc);
            }
            assert!(val < ub);
            assert_eq!(ub, ub_);
            self.ctlp += 1;
            self.tracebuf.push(TraceEntry::Replay(entry));
            return Ok(val);
          }
          ReplayLogEntry::DrawRot{..} => {
            unimplemented!();
          }
        }
      }
      if self.comp <= self.ctlp && (self.ctlp as usize) < self.buf.len() {
        let entry = self.buf[self.ctlp as usize];
        match entry {
          ReplayLogEntry::Draw{val, ub, ..} => {
            if self.trace {
              //println!("TRACE:  ReplayLog::_next_draw: comp={} ctlp={} v={} ub={} post  loc={:?}", self.comp, self.ctlp, val, ub, loc);
            }
            assert!(val < ub);
            assert_eq!(ub, ub_);
            self.ctlp += 1;
            self.tracebuf.push(TraceEntry::Replay(entry));
            return Ok(val);
          }
          ReplayLogEntry::DrawRot{val, ub, rot, ..} => {
            assert!(val < ub);
            assert_eq!(ub, ub_);
            self.ctlp += 1;
            self.tracebuf.push(TraceEntry::Replay(entry));
            return Ok((val + rot) % ub);
          }
        }
      }
      break;
    }
    if self.buf.len() == self.ctlp as usize {
      if self.trace {
        //println!("TRACE:  ReplayLog::_next_draw: comp={} ctlp={} v={} ub={} fresh loc={:?}", self.comp, self.ctlp, val, ub, loc);
      }
      // FIXME FIXME: pv cache.
      let rot = if self.pivp < self.ctlp {
        let StaticLoc_::L1(loc_) = loc_;
        match self.pv_cache.last() {
          Some(pv) => {
            let pvbuf = &pv.buf;
            let dp = match self.draw_ptr.get(&loc_) {
              None => self.pivp,
              Some(&dp) => dp
            };
            let mut rot_ = None;
            for p in dp + 1 .. pvbuf.len() as u32 {
              match &pvbuf[p as usize] {
                &ReplayLogEntry::Draw{val, loc, ..} => {
                  // FIXME: check ub_, ub.
                  let StaticLoc_::L1(loc) = loc;
                  if loc_ == loc {
                    self.draw_ptr.insert(loc_, p);
                    rot_ = Some(val);
                    break;
                  }
                }
                &ReplayLogEntry::DrawRot{val, ub, rot, loc} => {
                  // FIXME: check ub_, ub.
                  let StaticLoc_::L1(loc) = loc;
                  if loc_ == loc {
                    self.draw_ptr.insert(loc_, p);
                    // NB: both choices below are currently the same
                    // perfwise (saving ~1% of backtracks).
                    /*rot_ = Some(rot);*/
                    rot_ = Some((val + rot) % ub);
                    break;
                  }
                }
              }
            }
            if dp < (pvbuf.len() as u32) && rot_.is_none() {
              self.draw_ptr.insert(loc_, pvbuf.len() as u32);
            }
            rot_
          }
          None => None
        }
      } else {
        None
      };
      let val = 0;
      let ub = ub_;
      let loc = loc_;
      self.ctlp += 1;
      match rot {
        Some(rot) => {
          if rot > 0 {
            let entry = ReplayLogEntry::DrawRot{val, ub, rot, loc};
            self.buf.push(entry);
            self.tracebuf.push(TraceEntry::Fresh_(entry).into());
            return Ok((val + rot) % ub);
          } else {
            let entry = ReplayLogEntry::Draw{val, ub, loc};
            self.buf.push(entry);
            self.tracebuf.push(TraceEntry::Fresh_(entry).into());
            return Ok(val);
          }
        }
        None => {
          let entry = ReplayLogEntry::Draw{val, ub, loc};
          self.buf.push(entry);
          self.tracebuf.push(TraceEntry::Fresh_(entry).into());
          return Ok(val);
        }
      }
    }
    unreachable!();
  }

  /*pub fn _commit(&mut self) {
    if self.comp < self.ctlp {
      self.comp = self.ctlp;
    }
  }*/

  pub fn _backtrace(&mut self, /*loc: StaticLoc*/) {
    for p in (self.comp .. self.ctlp).rev() {
      if self.trace {
        match &self.buf[p as usize] {
          &ReplayLogEntry::Draw{ref val, ub, loc} => {
            let next_val = *val + 1;
            if next_val < ub {
              println!("TRACE:  ReplayLog::_backtrace: comp={} ctlp={} p={} nval={} ub={} loc={:?}", self.comp, self.ctlp, p, next_val, ub, loc);
              for q in (0 .. self.ctlp).rev() {
                if q == self.comp {
                  println!("TRACE:  ReplayLog::_backtrace:   log[{}]={:?} commit", q, &self.buf[q as usize]);
                } else {
                  println!("TRACE:  ReplayLog::_backtrace:   log[{}]={:?}", q, &self.buf[q as usize]);
                }
              }
              for k in (0 .. self.tracebuf.len()).rev() {
                println!("TRACE:  ReplayLog::_backtrace:   trace[{}]={:?}", k, &self.tracebuf[k]);
              }
            }
          }
          _ => {}
        }
      }
      match &mut self.buf[p as usize] {
        &mut ReplayLogEntry::Draw{ref mut val, ub, ..} |
        &mut ReplayLogEntry::DrawRot{ref mut val, ub, ..} => {
          let next_val = *val + 1;
          if next_val < ub {
            self.btct += 1;
            if self.btct >= self.btub {
              self.fail = true;
              return;
            }
            *val = next_val;
            self.pivp = p;
            self.buf.truncate((p + 1) as usize);
            return;
          }
        }
      }
    }
    if self.trace {
      println!("TRACE:  ReplayLog::_backtrace: comp={} ctlp={} fail", self.comp, self.ctlp);
      for q in (0 .. self.ctlp).rev() {
        if q == self.comp {
          println!("TRACE:  ReplayLog::_backtrace:   log[{}]={:?} commit", q, &self.buf[q as usize]);
        } else {
          println!("TRACE:  ReplayLog::_backtrace:   log[{}]={:?}", q, &self.buf[q as usize]);
        }
      }
      for k in (0 .. self.tracebuf.len()).rev() {
        println!("TRACE:  ReplayLog::_backtrace:   trace[{}]={:?}", k, &self.tracebuf[k]);
      }
    }
    self.btct += 1;
    self.fail = true;
  }
}

pub struct EmitMatch {
  trace: bool,
  newbest: bool,
  bestp: u32,
  matp: u32,
  pat:  Option<String>,
  ictr: i64,
}

impl Default for EmitMatch {
  fn default() -> EmitMatch {
    EmitMatch{
      trace: false,
      newbest: false,
      bestp: 0,
      matp: 0,
      pat:  None,
      ictr: 0,
    }
  }
}

impl EmitMatch {
  pub fn set_trace(&mut self, flag: bool) {
    self.trace = flag;
  }

  pub fn _reset(&mut self) {
    self.newbest = false;
    self.bestp = 0;
    self.matp = 0;
    //self.pat = None;
    self.ictr = 0;
  }

  pub fn rewind(&mut self) {
    self.newbest = false;
    self.matp = 0;
  }

  pub fn unset_pat(&mut self) {
    self.pat = None;
  }

  pub fn set_pat(&mut self, pat: &str) {
    //println!("DEBUG:  set_pat: pat=\"{}\"", pat);
    self.pat = Some(String::new());
    self.pat.as_mut().unwrap().push_str(pat);
    //println!("DEBUG:  set_pat: pat={:?}", self.pat);
  }
}

pub enum DrawMode {
  _Top,
  Rng{init: u64, rng: Rc<RefCell<ChaCha20Stream>>},
  Replay{log: ReplayLog},
}

impl Default for DrawMode {
  fn default() -> DrawMode {
    DrawMode::_Top
  }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct StaticLoc(&'static Location<'static>);

impl Debug for StaticLoc {
  fn fmt(&self, f: &mut Formatter) -> FmtResult {
    write!(f, " line={} col={} ", self.0.line(), self.0.column())
  }
}

#[derive(Clone, Copy, Debug)]
pub enum StaticLoc_ {
  L1(StaticLoc),
  //L2(StaticLoc, StaticLoc),
}

impl From<StaticLoc> for StaticLoc_ {
  fn from(loc: StaticLoc) -> StaticLoc_ {
    StaticLoc_::L1(loc)
  }
}

//#[derive(Default)]
pub struct StaticCache {
  latex_name_trie: CharTrie,
  trie: FxHashMap<StaticLoc, CharTrie>,
}

impl Default for StaticCache {
  fn default() -> StaticCache {
    let mut latex_name_trie = CharTrie::default();
    let mut idx = 0;
    for u in 0 .. 26 {
      let c = (b'A' + u) as char;
      for prime in 0 .. 2 {
        let mut v = String::new();
        v.push(c);
        if prime == 1 {
          v.push('\'');
        }
        latex_name_trie.insert(&v, idx);
        idx += 1;
        // FIXME FIXME: subscript hack.
        for sub in 0 .. 9 {
          let vlen = v.len();
          match sub {
            0 => {
              v.push_str("_0");
            }
            1 => {
              v.push_str("_1");
            }
            2 => {
              v.push_str("_2");
            }
            3 => {
              v.push_str("_3");
            }
            4 => {
              v.push_str("_4");
            }
            5 => {
              v.push_str("_A");
            }
            6 => {
              v.push_str("_B");
            }
            7 => {
              v.push_str("_C");
            }
            8 => {
              v.push_str("_D");
            }
            _ => unimplemented!()
          }
          latex_name_trie.insert(&v, idx);
          idx += 1;
          v.truncate(vlen);
        }
      }
    }
    for u in 0 .. 26 {
      let c = (b'a' + u) as char;
      for prime in 0 .. 2 {
        let mut v = String::new();
        v.push(c);
        if prime == 1 {
          v.push('\'');
        }
        latex_name_trie.insert(&v, idx);
        idx += 1;
        // FIXME FIXME: subscript hack.
        for sub in 0 .. 9 {
          let vlen = v.len();
          match sub {
            0 => {
              v.push_str("_0");
            }
            1 => {
              v.push_str("_1");
            }
            2 => {
              v.push_str("_2");
            }
            3 => {
              v.push_str("_3");
            }
            4 => {
              v.push_str("_4");
            }
            5 => {
              v.push_str("_A");
            }
            6 => {
              v.push_str("_B");
            }
            7 => {
              v.push_str("_C");
            }
            8 => {
              v.push_str("_D");
            }
            _ => unimplemented!()
          }
          latex_name_trie.insert(&v, idx);
          idx += 1;
          v.truncate(vlen);
        }
      }
    }
    for v0 in [
        "\\omega",
        "\\ell",
        "\\Gamma",
        "\\Omega",
        "\\gamma",
    ].iter() {
      for prime in 0 .. 2 {
        let mut v = String::new();
        v.push_str(v0);
        if prime == 1 {
          v.push('\'');
        }
        latex_name_trie.insert(&v, idx);
        idx += 1;
        // FIXME FIXME: subscript hack.
        for sub in 0 .. 9 {
          let vlen = v.len();
          match sub {
            0 => {
              v.push_str("_0");
            }
            1 => {
              v.push_str("_1");
            }
            2 => {
              v.push_str("_2");
            }
            3 => {
              v.push_str("_3");
            }
            4 => {
              v.push_str("_4");
            }
            5 => {
              v.push_str("_A");
            }
            6 => {
              v.push_str("_B");
            }
            7 => {
              v.push_str("_C");
            }
            8 => {
              v.push_str("_D");
            }
            _ => unimplemented!()
          }
          latex_name_trie.insert(&v, idx);
          idx += 1;
          v.truncate(vlen);
        }
      }
    }
    StaticCache{
      latex_name_trie,
      trie: FxHashMap::default(),
    }
  }
}

#[derive(Default)]
pub struct Geometry {
  mode: DrawMode,
  ematch: EmitMatch,
  static_cache: StaticCache,
  trace: bool,
  math: bool,
  ctr: i8,
  itemctr: u32,
  prevstage: Vec<(ItemNum, Item_)>,
  stage: Vec<(ItemNum, Item_)>,
  items: BTreeMap<ItemNum, Item_>,
  nodes: BTreeMap<ItemNum, INode_>,
  tree_: TreeState,
  query: RefCell<QueryState>,
  name_tab: BTreeMap<SNum, Name_>,
  name_inv: BTreeMap<Name_, SNum>,
  name_map: BTreeMap<SNum, Name>,
  name_idx: BTreeSet<(SmolStr, SNum)>,
}

impl Geometry {
  pub fn reset_rng(&mut self, init: u64, rng: Rc<RefCell<ChaCha20Stream>>) {
    self.mode = DrawMode::Rng{init, rng};
    self._reset();
  }

  pub fn reset_replay(&mut self) {
    self.mode = DrawMode::Replay{log: ReplayLog::default()};
    self._reset();
  }

  pub fn set_backtrace_limit(&mut self, btub: i32) {
    match &mut self.mode {
      &mut DrawMode::Replay{ref mut log} => {
        log.btub = btub;
      }
      _ => unimplemented!()
    }
  }

  pub fn set_trace(&mut self, trace: bool) {
    match &mut self.mode {
      &mut DrawMode::Replay{ref mut log} => {
        log.set_trace(trace);
      }
      _ => {}
    }
    self.ematch.set_trace(trace);
    self.trace = trace;
  }

  pub fn _reset(&mut self) {
    self.ematch._reset();
    self.math = false;
    self.ctr = 0;
    self.name_tab.clear();
    self.name_inv.clear();
    self.name_map.clear();
    self.name_idx.clear();
  }

  pub fn rewind(&mut self) {
    match &mut self.mode {
      &mut DrawMode::Rng{init, ref rng} => {
        rng.borrow_mut().seek(SeekFrom::Start(init)).unwrap();
      }
      &mut DrawMode::Replay{ref mut log} => {
        log.rewind();
      }
      _ => unimplemented!()
    }
    self.ematch.rewind();
    self.math = false;
    self.ctr = 0;
    self.name_tab.clear();
    self.name_inv.clear();
    self.name_map.clear();
    self.name_idx.clear();
  }

  pub fn _backtrace_count(&self) -> i32 {
    match &self.mode {
      &DrawMode::Replay{ref log} => {
        log.btct
      }
      _ => 0
    }
  }

  pub fn _pv_cache(&self) -> &[PvCacheEntry] {
    match &self.mode {
      &DrawMode::Replay{ref log} => {
        &log.pv_cache
      }
      _ => unimplemented!()
    }
  }

  pub fn emit_longest_str(&self) -> &str {
    self.ematch.pat.as_ref().unwrap().get( .. self.ematch.bestp as usize).unwrap()
  }

  pub fn emit_str(&self) -> &str {
    self.ematch.pat.as_ref().unwrap().get( .. self.ematch.matp as usize).unwrap()
  }

  pub fn _emit_pat(&self) -> &str {
    self.ematch.pat.as_ref().unwrap()
  }

  pub fn _names(&self) -> &BTreeMap<SNum, Name> {
    &self.name_map
  }

  pub fn _items(&self) -> impl Iterator<Item=(ItemNum, &Item_)> {
    self.items.iter().map(|(&i, item)| (i, item))
  }

  pub fn _node_lookup(&self, i: ItemNum) -> Option<&INode_> {
    self.nodes.get(&i)
  }

  pub fn _nodes(&self) -> impl Iterator<Item=(ItemNum, &INode_)> {
    self.nodes.iter().map(|(&i, node)| (i, node))
  }

  pub fn _root(&self) -> Option<(ItemNum, &Node_)> {
    self.tree_.root.map(|r| (r, &**self.nodes.get(&r).unwrap().node.as_ref().unwrap()))
  }

  pub fn _roots(&self) -> impl Iterator<Item=ItemNum> + '_ {
    self.tree_.rootstop.iter().map(|&(i, _)| i)
  }

  pub fn _debug_dump(&self) {
    if self.ematch.newbest {
      println!("DEBUG:  Geometry::_debug_dump: new best");
    }
    println!("DEBUG:  Geometry::_debug_dump: s=\"{}\"", self.emit_str());
    for (&i, item) in self.items.iter() {
      println!("DEBUG:  Geometry::_debug_dump: item[{:?}]={:?}", i, item);
    }
    for k in 0 .. self.tree_.rootstop.len() {
      println!("DEBUG:  Geometry::_debug_dump: tree.rootstop[{}]={:?}", k, &self.tree_.rootstop[k]);
    }
    println!("DEBUG:  Geometry::_debug_dump: tree.root={:?}", &self.tree_.root);
    println!("DEBUG:  Geometry::_debug_dump: tree.sup ={:?}", &self.tree_.sup);
    println!("DEBUG:  Geometry::_debug_dump: tree.jux ={:?}", &self.tree_.jux);
    for (&i, node) in self.nodes.iter() {
      println!("DEBUG:  Geometry::_debug_dump: node[{:?}]={:?}", i, node);
    }
    match &self.mode {
      &DrawMode::Replay{ref log} => {
        println!("DEBUG:  Geometry::_debug_dump: btct={:?}", log.btct);
      }
      _ => {}
    }
  }

  pub fn draw(&mut self) -> Result<(), ()> {
    loop {
      self.rewind();
      match self._redraw() {
        Ok(_) => {
          let res = self.halt();
          if res.is_ok() {
            return Ok(());
          }
        }
        Err(_) => {
          match &self.mode {
            &DrawMode::Replay{ref log} => {
              if log.fail {
                return Err(());
              }
            }
            _ => {}
          }
        }
      }
    }
    //Err(())
  }

  pub fn match_<P: AsRef<str>>(&mut self, pat: P) -> Result<(), ()> {
    let pat = pat.as_ref();
    self.ematch.set_pat(pat);
    loop {
      self.rewind();
      let e = match self._redraw() {
        Ok(_) => {
          let res = self.halt();
          match res {
            Ok(_) => {
              self._backtrace(Ok(()));
              return Ok(());
            }
            Err(e) => e.into()
          }
        }
        Err(e) => {
          // FIXME: search here (???).
          e
        }
      };
      if self.trace {
        println!("TRACE:  Geometry::match_: err: e={:?}", e);
        self._debug_dump();
      }
      self._backtrace(Err(e));
      match &self.mode {
        &DrawMode::Replay{ref log} => {
          // NB: log.fail set by ReplayLog::_backtrace().
          if log.fail {
            return Err(());
          }
        }
        _ => {}
      }
    }
    //Err(())
  }

  #[track_caller]
  pub fn draw_uni(&mut self, ub: UDraw) -> Result<UDraw, ()> {
    if ub == 1 {
      return Ok(0);
    }
    let loc = StaticLoc(Location::caller()).into();
    match &mut self.mode {
      &mut DrawMode::Rng{ref rng, ..} => {
        Ok(FastRangeU32::new(ub as u32).draw(&mut *rng.borrow_mut()) as UDraw)
      }
      &mut DrawMode::Replay{ref mut log} => {
        log._next_draw(ub, loc)
      }
      _ => unimplemented!()
    }
  }

  #[track_caller]
  pub fn nil_decode(&self) -> Result<AttrStr, ()> {
    //let loc = StaticLoc(Location::caller()).into();
    let pos = self.ematch.matp as usize;
    let s = AttrStr{start: pos as u32, end: pos as u32, val: "".into()};
    Ok(s)
  }

  #[track_caller]
  pub fn eof_decode(&self) -> Result<AttrStr, ()> {
    //let loc = StaticLoc(Location::caller()).into();
    let pos = self.ematch.matp as usize;
    if pos != self.ematch.pat.as_ref().unwrap().len() {
      // FIXME: err loc.
      return Err(());
      //return Err(Err_::Bot(loc));
    }
    let s = AttrStr{start: pos as u32, end: pos as u32, val: "".into()};
    Ok(s)
  }

  #[track_caller]
  pub fn maybe_exact_decode_trie<S: AsRef<[&'static str]>>(&mut self, set: S) -> Result<Option<AttrStr>, ()> {
    let loc = StaticLoc(Location::caller()).into();
    self._decode_trie(set, true, false, loc)
  }

  #[track_caller]
  pub fn maybe_auto_decode_trie<S: AsRef<[&'static str]>>(&mut self, set: S) -> Result<Option<AttrStr>, ()> {
    let loc = StaticLoc(Location::caller()).into();
    self._decode_trie(set, true, true, loc)
  }

  #[track_caller]
  pub fn exact_decode_trie<S: AsRef<[&'static str]>>(&mut self, set: S) -> Result<AttrStr, ()> {
    let loc = StaticLoc(Location::caller()).into();
    self._decode_trie(set, false, false, loc).map(|r| r.unwrap())
  }

  #[track_caller]
  pub fn auto_decode_trie<S: AsRef<[&'static str]>>(&mut self, set: S) -> Result<AttrStr, ()> {
    let loc = StaticLoc(Location::caller()).into();
    self._decode_trie(set, false, true, loc).map(|r| r.unwrap())
  }

  pub fn _decode_trie<S: AsRef<[&'static str]>>(&mut self, set: S, empty: bool, upper: bool, loc: StaticLoc) -> Result<Option<AttrStr>, ()> {
    if let None = self.static_cache.trie.get(&loc) {
      let mut trie = CharTrie::default();
      let set = set.as_ref();
      for (idx, key) in set.iter().enumerate() {
        if key.is_empty() {
          if !empty {
            panic!("bug");
          }
        } else {
          let mut s_ = None;
          if upper {
            let mut cs = key.chars();
            match cs.next() {
              Some(' ') => {
                match cs.next() {
                  None => {}
                  Some(c) => {
                    let u = c.to_ascii_uppercase();
                    if u != c {
                      let mut s2 = String::new();
                      s2.push(' ');
                      s2.push(u);
                      for c in cs {
                        s2.push(c);
                      }
                      s_ = Some(s2);
                    }
                  }
                }
              }
              Some(c) => {
                let u = c.to_ascii_uppercase();
                if u != c {
                  let mut s2 = String::new();
                  s2.push(u);
                  for c in cs {
                    s2.push(c);
                  }
                  s_ = Some(s2);
                }
              }
              _ => {}
            }
          }
          assert!(idx < u32::max_value() as usize);
          let val = idx as u32;
          if let Some(key) = s_.as_ref() {
            trie.insert(key, val);
          }
          trie.insert(key, val);
        }
      }
      assert!(self.static_cache.trie.insert(loc, trie).is_none());
    }
    if let Some(trie) = self.static_cache.trie.get(&loc) {
      let start = self.ematch.matp as usize;
      match trie.match_(self.ematch.pat.as_ref().unwrap().get(start .. ).unwrap()) {
        None => {
          if !empty {
            Err(())
          } else {
            Ok(None)
          }
        }
        Some((off, _)) => {
          let end = start + off;
          let key = self.ematch.pat.as_ref().unwrap().get(start .. end).unwrap();
          self.ematch.matp = end as u32;
          if self.ematch.bestp < self.ematch.matp {
            self.ematch.newbest = true;
            self.ematch.bestp = self.ematch.matp;
          }
          let s = AttrStr{start: start as u32, end: end as u32, val: key.into()};
          match &mut self.mode {
            &mut DrawMode::Replay{ref mut log} => {
              log.tracebuf.push(TraceEntry::Decode(s.clone()).into());
            }
            _ => {}
          }
          Ok(Some(s))
        }
      }
    } else {
      unreachable!();
    }
  }

  //#[track_caller]
  pub fn decode_latex_name_(&mut self) -> Result<(AttrStr, SNum), ()> {
    // FIXME: spaces.
    // FIXME: rep.
    if self.math {
      // FIXME: math mode.
    } else {
      self.exact_decode_trie(["$", "$$", "\\(", "\\["])?;
      self.math = true;
    }
    let start = self.ematch.matp as usize;
    let mut cursor = start;
    //let mut end = start;
    let mut first = true;
    let mut space = false;
    let mut end_mode = false;
    loop {
      if space {
        // FIXME: this messes w/ the decode trace order.
        let s = self.exact_decode_trie(["$", "$$", "\\)", "\\]", " "])?;
        if &s.val != " " {
          if self.math {
            self.math = false;
          } else {
            // FIXME: math mode.
            return Err(());
          }
          end_mode = true;
          break;
        }
        space = false;
        cursor += 1;
      }
      let pat = self.ematch.pat.as_ref().unwrap().get(cursor .. ).unwrap();
      if self.trace {
        //println!("DEBUG:  decode_latex_name_: start={} cursor={} first?{:?} space?{:?} pat=\"{}\"", start, cursor, first, space, pat);
      }
      match self.static_cache.latex_name_trie.match_(pat) {
        None => {
          //println!("DEBUG:  decode_latex_name_:   no match");
          if first {
            return Err(());
          }
          //println!("DEBUG:  decode_latex_name_:   break");
          break;
        }
        Some((off, _)) => {
          if self.trace {
            //println!("DEBUG:  decode_latex_name_:   match off={}", off);
          }
          let end = cursor + off;
          let key = self.ematch.pat.as_ref().unwrap().get(cursor .. end).unwrap();
          if key.get( .. 1).unwrap() == "\\" {
            if key.find("_").is_none() {
              space = true;
            }
          }
          self.ematch.matp = end as u32;
          if self.ematch.bestp < self.ematch.matp {
            self.ematch.newbest = true;
            self.ematch.bestp = self.ematch.matp;
          }
          cursor = end;
        }
      }
      first = false;
    }
    if !end_mode {
      self.exact_decode_trie(["$", "$$", "\\)", "\\]"])?;
      if self.math {
        self.math = false;
      } else {
        // FIXME: math mode.
        return Err(());
      }
    }
    let key = self.ematch.pat.as_ref().unwrap().get(start .. cursor).unwrap();
    if self.trace {
      //println!("DEBUG:  decode_latex_name_: start={} cursor={} val=\"{}\"", start, cursor, key);
    }
    let s = AttrStr{start: start as u32, end: cursor as u32, val: key.into()};
    match &mut self.mode {
      &mut DrawMode::Replay{ref mut log} => {
        log.tracebuf.push(TraceEntry::Decode(s.clone()).into());
      }
      _ => {}
    }
    match self.name_idx.range((s.val.clone(), SNum::nil()) .. ).next() {
      None => {}
      Some(&(ref o_val, ox)) => {
        // FIXME: distinctness test should be optional.
        if &s.val == o_val {
          return Ok((s, ox));
        }
      }
    }
    let x = self._fresh();
    self.name_idx.insert((s.val.clone(), x));
    self.name_map.insert(x, Name{kind: NameKind::LatexAtom, val: s.val.clone()});
    Ok((s, x))
  }

  pub fn _fresh(&mut self) -> SNum {
    let x = self.ctr + 1;
    assert!(x > 0);
    self.ctr = x;
    SNum(x)
  }

  pub fn halt(&mut self) -> Result<(), Err_> {
    if self.tree_.root.is_some() {
      self._recheck_root()?;
      let root = self.tree_.root.take().unwrap();
      self.tree_.rootstop.push((root, ItemNum::nil()));
      match &mut self.mode {
        &mut DrawMode::Replay{ref mut log} => {
          log.tracebuf.push(TraceEntry::RootStop_(root, ItemNum::nil()).into());
        }
        _ => {}
      }
    }
    match &mut self.mode {
      &mut DrawMode::Rng{..} => {
        //println!("DEBUG:  Geometry::done: rng");
      }
      &mut DrawMode::Replay{..} => {
        //println!("DEBUG:  Geometry::done: replay");
        if let Some(pat) = self.ematch.pat.as_ref() {
          //println!("DEBUG:  Geometry::done:   pat=\"{}\"", pat);
          //println!("DEBUG:  Geometry::done:   buf=\"{}\"", self.ematch.buf);
          //if &self.ematch.buf != pat {}
          if self.ematch.matp as usize != pat.len() {
            /*log.fail = true;*/
            return e_bot();
          }
        }
      }
      _ => unimplemented!()
    }
    // FIXME: set result state.
    /*self.res = Some(Ok(()));*/
    Ok(())
  }

  //pub fn _backtrace_loc(&mut self, /*loc: StaticLoc */) {}
  pub fn _backtrace(&mut self, res: Result<(), Err_>) {
    // FIXME FIXME: can't make this `-> Result<_>` due to silly
    // borrowck failure of `self._backtrace()?`.
    match &mut self.mode {
      &mut DrawMode::Rng{..} => {
        // FIXME: need to backtrace here too.
        unimplemented!();
      }
      &mut DrawMode::Replay{ref mut log} => {
        // FIXME: log caller loc.
        if self.ematch.newbest {
          let e = PvCacheEntry{
            matp: self.ematch.bestp,
            btct: log.btct,
            res,
            buf:  log.buf.clone(),
          };
          log.pv_cache.push(e);
        }
        log._backtrace(/*loc*/);
      }
      _ => unimplemented!()
    }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct ItemNum(u32);

impl ItemNum {
  pub fn nil() -> ItemNum {
    ItemNum(0)
  }

  pub fn _succ(&self) -> ItemNum {
    ItemNum(self.0 + 1)
  }
}

#[derive(Clone, Copy, Debug)]
pub enum Err_ {
  OG,
  Top(StaticLoc),
  Bot(StaticLoc),
}

impl From<()> for Err_ {
  #[inline]
  fn from(_: ()) -> Err_ {
    Err_::OG
  }
}

#[track_caller]
pub fn e_top() -> Result<(), Err_> {
  let loc = StaticLoc(Location::caller()).into();
  Err(Err_::Top(loc))
}

#[track_caller]
pub fn e_bot() -> Result<(), Err_> {
  let loc = StaticLoc(Location::caller()).into();
  Err(Err_::Bot(loc))
}

#[track_caller]
pub fn _e_bot() -> Err_ {
  let loc = StaticLoc(Location::caller()).into();
  Err_::Bot(loc)
}

pub trait Top {
  fn top() -> Self where Self: Sized;
}

pub fn top<T: Top>() -> T {
  <T as Top>::top()
}

#[derive(Clone, Debug)]
#[non_exhaustive]
#[repr(u8)]
pub enum CtlKind {
  Comma,
  CommaAnd,
  And,
  Of,
  Whose,
  With,
  At,
  In,
  On,
  Through,
  From,
  Again,
}

impl CtlKind {
  pub fn from<S: AsRef<str>>(ctl_s: S) -> CtlKind {
    match ctl_s.as_ref() {
      "," => {
        CtlKind::Comma
      }
      ", and" => {
        CtlKind::CommaAnd
      }
      "and" => {
        CtlKind::And
      }
      "of" => {
        CtlKind::Of
      }
      "whose" => {
        CtlKind::Whose
      }
      "with" => {
        CtlKind::With
      }
      "at" => {
        CtlKind::At
      }
      "in" => {
        CtlKind::In
      }
      "on" => {
        CtlKind::On
      }
      "through" => {
        CtlKind::Through
      }
      "from" => {
        CtlKind::From
      }
      "again" => {
        CtlKind::Again
      }
      _ => unimplemented!()
    }
  }
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct ItemKind {
  bits: u16,
}

impl Debug for ItemKind {
  fn fmt(&self, f: &mut Formatter) -> FmtResult {
    if (*self & ItemKind::name_()).is_some() {
      write!(f, "ItemKind(Name_)")
    } else if (*self & ItemKind::head_()).is_some() {
      write!(f, "ItemKind(Head_)")
    } else if (*self & ItemKind::phead_()).is_some() {
      write!(f, "ItemKind(PHead_)")
    } else if (*self & ItemKind::unify_()).is_some() {
      write!(f, "ItemKind(Unify_)")
    } else if (*self & ItemKind::pred_()).is_some() {
      write!(f, "ItemKind(Pred_)")
    } else if (*self & ItemKind::arg0_()).is_some() {
      write!(f, "ItemKind(Arg0_)")
    } else if (*self & ItemKind::ctl_()).is_some() {
      write!(f, "ItemKind(Ctl_)")
    } else if self.bits == 1 << 15 {
      write!(f, "ItemKind(Stop_)")
    } else {
      write!(f, "ItemKind(bits={:b})", self.bits)
    }
  }
}

impl ItemKind {
  #[inline] pub fn name_()  -> ItemKind { ItemKind{bits: 1 << 0} }
  #[inline] pub fn head_()  -> ItemKind { ItemKind{bits: 1 << 1} }
  #[inline] pub fn phead_() -> ItemKind { ItemKind{bits: 1 << 2} }
  #[inline] pub fn unify_() -> ItemKind { ItemKind{bits: 1 << 3} }
  #[inline] pub fn pred_()  -> ItemKind { ItemKind{bits: 1 << 4} }
  #[inline] pub fn arg0_()  -> ItemKind { ItemKind{bits: 1 << 5} }
  //#[inline] pub fn quant_() -> ItemKind { ItemKind{bits: 1 << 5} }
  //#[inline] pub fn ldesc_() -> ItemKind { ItemKind{bits: 1 << 6} }
  #[inline] pub fn ctl_()   -> ItemKind { ItemKind{bits: 1 << 7} }

  #[inline]
  pub fn empty() -> ItemKind {
    ItemKind{bits: 0}
  }

  #[inline]
  pub fn is_empty(&self) -> bool {
    self.bits == 0
  }
}

impl Optional for ItemKind {
  #[inline]
  fn is_none(&self) -> bool {
    self.is_empty()
  }
}

impl BitAnd for ItemKind {
  type Output = ItemKind;

  #[inline]
  fn bitand(self, rhs: ItemKind) -> ItemKind {
    ItemKind{bits: self.bits & rhs.bits}
  }
}

impl BitOr for ItemKind {
  type Output = ItemKind;

  #[inline]
  fn bitor(self, rhs: ItemKind) -> ItemKind {
    ItemKind{bits: self.bits | rhs.bits}
  }
}

impl Sub for ItemKind {
  type Output = ItemKind;

  #[inline]
  fn sub(self, rhs: ItemKind) -> ItemKind {
    ItemKind{bits: self.bits & !rhs.bits}
  }
}

impl Item_ {
  #[inline]
  pub fn kind(&self) -> ItemKind {
    match self {
      &Item_::Name_(..)   => ItemKind::name_(),
      &Item_::Head_(..)   => ItemKind::head_(),
      &Item_::PHead_(..)  => ItemKind::phead_(),
      &Item_::Unify_(..)  => ItemKind::unify_(),
      &Item_::Pred_(..)   => ItemKind::pred_(),
      &Item_::Arg0_(..)   => ItemKind::arg0_(),
      &Item_::Ctl_(..)    => ItemKind::ctl_(),
      &Item_::Stop_(..)   |
      &Item_::Sep_(..)    => ItemKind{bits: 1 << 15},
      _ => unimplemented!()
    }
  }
}

pub type ItemRef = Rc<Item_>;

#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum Item_ {
  Stop_(AttrStr),
  Sep_(AttrStr),
  Name_(AttrStr, SNum, Vec<ItemNum>),
  Head_(AttrStr, HeadQuant_, Vec<ItemNum>),
  Unify_(AttrStr, Option<ItemNum>, Vec<ItemNum>),
  PHead_(AttrStr, Vec<ItemNum>),
  Pred_(AttrStr, Option<ItemNum>, Vec<ItemNum>),
  //Desc(AttrStr),
  Arg0_(AttrStr, Vec<ItemNum>),
  Ctl_(AttrStr, /*Vec<ItemNum>,*/ Option<ItemNum>),
}

impl Item_ {
  pub fn name_(s: AttrStr, x: SNum) -> Item_ {
    Item_::Name_(s, x, Vec::new())
  }

  pub fn head_(s: AttrStr) -> Item_ {
    Item_::Head_(s, HeadQuant_::One, Vec::new())
    //Item_::Head_(s, QuantArg::Top, Vec::new())
  }

  pub fn mult_head_<S: Into<Option<AttrStr>>>(s: AttrStr, qs: S) -> Item_ {
    if let Some(qs) = qs.into() {
      Item_::Head_(s, HeadQuant_::Mult(qs), Vec::new())
      //Item_::Head_(s, QuantArg::Mult_(qs), Vec::new())
    } else {
      Item_::Head_(s, HeadQuant_::MultAnon, Vec::new())
      //Item_::Head_(s, QuantArg::Mult, Vec::new())
    }
  }

  pub fn unify_(s: AttrStr) -> Item_ {
    Item_::Unify_(s, None, Vec::new())
  }

  pub fn pred_(s: AttrStr) -> Item_ {
    Item_::Pred_(s, None, Vec::new())
  }
}

pub type NodeRef = Rc<Node_>;

#[derive(Clone, Debug)]
pub struct INode_ {
  // TODO TODO
  ub:   ItemNum,
  //comp: ItemNum,
  //lb:   u16,
  //ub:   u16,
  node: Option<NodeRef>,
}

impl INode_ {
  #[inline]
  pub fn top() -> INode_ {
    INode_ {
      ub:   ItemNum::nil(),
      //comp: ItemNum::nil(),
      //lb:   0,
      //ub:   u16::max_value(),
      node: None,
    }
  }

  #[inline]
  pub fn new(i: ItemNum, node: Node_) -> INode_ {
    INode_{
      ub:   i,
      //comp: i,
      //lb:   0,
      //ub:   u16::max_value(),
      node: Some(node.into()),
    }
  }
}

#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub enum NodeKind {
  // TODO
  Name,
  Head,
  Pair,
  Apply,
  Subst,
  Mult,
  //FHead,
  PHead,
  Prefix,
  Pred,
  Unify,
  Arg0,
  //PSeq,
  //PSeq,
  //Desc,
  Ctl,
  CtlPair,
}

#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum Node_ {
  // TODO
  Name(AttrStr, SNum),
  Head(AttrStr, HeadQuant_, Vec<(NodeRef, NodeRef)>),
  Pair(Option<NodeRef>, Option<NodeRef>),
  Apply(AttrStr, Option<NodeRef>, Option<NodeRef>, Vec<(NodeRef, NodeRef)>),
  // NB: Subst(X, Y) --> "X (with Y)".
  Subst(AttrStr, Option<NodeRef>, Option<NodeRef>),
  //Mult(Vec<NodeRef>),
  //Mult(Vec<(Option<AttrStr>, NodeRef)>),
  Mult(Vec<(Option<NodeRef>, NodeRef)>),
  //Quant(AttrStr),
  //FHead(...),
  PHead(AttrStr, /*Vec<(NodeRef, NodeRef)>*/),
  //PApply(..),
  Prefix(Vec<NodeRef>, Option<NodeRef>),
  Pred(AttrStr, Option<NodeRef>, Option<NodeRef>, Vec<(NodeRef, Option<NodeRef>)>),
  Unify(AttrStr, Option<NodeRef>, Option<NodeRef>),
  Tup2(()),
  Arg0(AttrStr, Option<NodeRef>, /*Vec<(NodeRef, NodeRef)>*/),
  PSeq(Vec<NodeRef>),
  //PSeq(Option<NodeRef>, Vec<NodeRef>, Option<NodeRef>),
  Desc(AttrStr),
  Ctl(AttrStr),
  CtlPair(NodeRef, NodeRef),
}

impl Node_ {
  pub fn kind(&self) -> Option<NodeKind> {
    Some(match self {
      &Node_::Name(..) => NodeKind::Name,
      &Node_::Head(..) => NodeKind::Head,
      &Node_::Pair(..) => NodeKind::Pair,
      &Node_::Apply(..) => NodeKind::Apply,
      &Node_::Subst(..) => NodeKind::Subst,
      &Node_::Mult(..) => NodeKind::Mult,
      &Node_::PHead(..) => NodeKind::PHead,
      &Node_::Prefix(..) => NodeKind::Prefix,
      &Node_::Pred(..) => NodeKind::Pred,
      &Node_::Unify(..) => NodeKind::Unify,
      &Node_::Arg0(..) => NodeKind::Arg0,
      &Node_::Ctl(..) => NodeKind::Ctl,
      &Node_::CtlPair(..) => NodeKind::CtlPair,
      _ => return None
    })
  }
}

#[derive(Clone, Debug)]
pub enum HeadQuant_ {
  // TODO TODO
  Top,
  One,
  MultAnon,
  Mult(AttrStr),
}

#[derive(Default)]
pub struct TreeState {
  // FIXME FIXME: seq of prev (Sep, Stop) roots.
  rootstop: Vec<(ItemNum, ItemNum)>,
  root: Option<ItemNum>,
  sup:  BTreeMap<ItemNum, ItemNum>,
  jux:  BTreeMap<ItemNum, ItemNum>,
  //diff: Vec<ItemNum>,
  recomp: BTreeSet<ItemNum>,
}

impl TreeState {
  pub fn _reset(&mut self) {
    // TODO
    self.rootstop.clear();
    self.root = None;
    self.sup.clear();
    self.jux.clear();
    self.recomp.clear();
  }
}

#[derive(Default)]
pub struct QueryState {
  // TODO
  pop_done: bool,
  pop_ub:   Option<ItemNum>,
  iter_set: BTreeSet<ItemNum>,
}

impl QueryState {
  pub fn _reset(&mut self) {
    // TODO
    self.pop_done = false;
    self.pop_ub = None;
    self.iter_set.clear();
  }
}

#[derive(Clone, Copy, Debug)]
pub struct RenderConfig {
  pub attr: bool,
}

impl Default for RenderConfig {
  fn default() -> RenderConfig {
    RenderConfig{
      attr: true,
    }
  }
}

impl Geometry {
  pub fn _node_recheck(&self, node: &Node_) -> Result<(), Err_> {
    'outer: loop {
      match node {
        &Node_::Mult(ref rev_args) => {
          if rev_args.len() <= 1 {
            return e_bot();
          }
        }
        &Node_::Pair(ref larg, ref rarg) => {
          // FIXME FIXME
          let larg = &**larg.as_ref().ok_or_else(|| _e_bot())?;
          let rarg = &**rarg.as_ref().ok_or_else(|| _e_bot())?;
          self._node_recheck(larg)?;
          self._node_recheck(rarg)?;
          match (larg, rarg) {
            (&Node_::Head(_, ref hquant, ..)
            ,&Node_::Name(..)) => {
              match hquant {
                &HeadQuant_::One => {}
                _ => return e_bot()
              }
            }
            (&Node_::Head(_, ref hquant, ..)
            ,&Node_::Mult(ref rev_args)) => {
              match hquant {
                &HeadQuant_::MultAnon |
                &HeadQuant_::Mult(_) => {
                  if rev_args.len() <= 1 {
                    return e_bot();
                  }
                }
                _ => return e_bot()
              }
            }
            _ => {}
          }
        }
        &Node_::Unify(_, ref larg, ref rarg) => {
          // FIXME FIXME
          let larg = &**larg.as_ref().ok_or_else(|| _e_bot())?;
          let rarg = &**rarg.as_ref().ok_or_else(|| _e_bot())?;
          self._node_recheck(larg)?;
          self._node_recheck(rarg)?;
          match (larg, rarg) {
            (&Node_::Head(_, ref hquant, ..)
            ,&Node_::Name(..)) |
            (&Node_::Name(..)
            ,&Node_::Head(_, ref hquant, ..)) => {
              match hquant {
                &HeadQuant_::One => {}
                _ => return e_bot()
              }
            }
            (&Node_::Head(_, ref hquant, ..)
            ,&Node_::Mult(ref rev_args)) |
            (&Node_::Mult(ref rev_args)
            ,&Node_::Head(_, ref hquant, ..)) => {
              match hquant {
                &HeadQuant_::MultAnon |
                &HeadQuant_::Mult(_) => {
                  if rev_args.len() <= 1 {
                    return e_bot();
                  }
                }
                _ => return e_bot()
              }
            }
            _ => {}
          }
        }
        &Node_::Pred(_, ref larg, ref rarg, ref ctl_args) => {
          // FIXME FIXME
          self._node_recheck(&**larg.as_ref().ok_or_else(|| _e_bot())?)?;
          //self._node_recheck(&**rarg.as_ref().ok_or_else(|| _e_bot())?)?;
          if let Some(rarg) = rarg.as_ref() {
            self._node_recheck(&**rarg)?;
          }
          for &(_, ref arg) in ctl_args.iter() {
            if let Some(arg) = arg.as_ref() {
              self._node_recheck(&**arg)?;
            }
          }
        }
        &Node_::Arg0(_, ref arg) => {
          // FIXME FIXME
          self._node_recheck(&**arg.as_ref().ok_or_else(|| _e_bot())?)?;
        }
        _ => {
        }
      }
      break 'outer;
    } // 'outer;
    Ok(())
  }

  pub fn _recheck_root(&self) -> Result<(), Err_> {
    if self.tree_.root.is_none() {
      return Ok(());
    }
    let root = self.tree_.root.unwrap();
    let root_node = match self.nodes.get(&root) {
      None => return e_bot(),
      Some(inode) => {
        if inode.node.is_none() {
          return e_bot();
        }
        inode.node.clone().unwrap()
      }
    };
    self._node_recheck(&*root_node)?;
    Ok(())
  }

  pub fn _node_render_praline(&self, cfg: RenderConfig, node: &Node_) -> Result<SmolStr, ()> {
    self._node_render_praline_(cfg, node, false)
  }

  pub fn _node_render_praline_(&self, cfg: RenderConfig, node: &Node_, hint_term: bool) -> Result<SmolStr, ()> {
    let mut buf = String::new();
    'outer: loop {
      match node {
        &Node_::Name(ref name_s, ..) => {
          buf.push_str("$");
          buf.push_str(&name_s.to_praline_str());
          buf.push_str("$");
          if cfg.attr {
          buf.push_str(&name_s.to_praline_attr());
          }
        }
        &Node_::Head(ref head_s, ..) => {
          buf.push_str("\"");
          buf.push_str(&head_s.to_praline_str());
          buf.push_str("\"");
          if cfg.attr {
          buf.push_str(&head_s.to_praline_attr());
          }
          if hint_term {
            buf.push_str("()");
          }
        }
        &Node_::Pair(ref larg, ref rarg) => {
          let larg_s = self._node_render_praline_(cfg, &**larg.as_ref().ok_or(())?, true)?;
          let rarg_s = self._node_render_praline(cfg, &**rarg.as_ref().ok_or(())?)?;
          /*buf.push_str(&rarg_s);
          buf.push_str(": ");
          buf.push_str(&larg_s);*/
          buf.push_str(&larg_s);
          buf.push_str(" -> ");
          buf.push_str(&rarg_s);
        }
        &Node_::Apply(ref _apply_s, ref larg, ref rarg, ref _ctl_args) => {
          // TODO TODO
          let larg_s = self._node_render_praline(cfg, &**larg.as_ref().ok_or(())?)?;
          let rarg_s = self._node_render_praline_(cfg, &**rarg.as_ref().ok_or(())?, true)?;
          // FIXME: examples of lmult case?
          let lmult = match &**larg.as_ref().ok_or(())? {
            &Node_::Mult(..) => true,
            _ => false
          };
          if lmult {
            buf.push_str("(");
          }
          buf.push_str(&larg_s);
          if lmult {
            buf.push_str(")");
          }
          buf.push_str("(");
          buf.push_str(&rarg_s);
          buf.push_str(")");
        }
        &Node_::Subst(ref _subst_s, ref larg, ref rarg, /*ref ctl_args*/) => {
          // TODO TODO
          let larg_s = self._node_render_praline_(cfg, &**larg.as_ref().ok_or(())?, true)?;
          buf.push_str(&larg_s);
          /*buf.push_str(" (where ");*/
          buf.push_str(" (with ");
          match &**rarg.as_ref().ok_or(())? {
            &Node_::Mult(ref r_rev_args) => {
              for (k, &(_, ref rarg)) in r_rev_args.iter().rev().enumerate() {
                if k > 0 {
                  buf.push_str(" , ");
                }
                let rarg_s = self._node_render_praline_(cfg, &**rarg, true)?;
                buf.push_str(&rarg_s);
              }
            }
            _ => {
              let rarg_s = self._node_render_praline_(cfg, &**rarg.as_ref().ok_or(())?, true)?;
              buf.push_str(&rarg_s);
            }
          }
          buf.push_str(" )");
        }
        &Node_::Mult(ref rev_args) => {
          for (k, &(_, ref arg)) in rev_args.iter().rev().enumerate() {
            if k > 0 {
              buf.push_str(",");
            }
            let arg_s = self._node_render_praline_(cfg, &**arg, hint_term)?;
            buf.push_str(&arg_s);
          }
        }
        &Node_::PHead(ref phead_s) => {
          buf.push_str("\"");
          buf.push_str(&phead_s.to_praline_str());
          buf.push_str("\"");
          if cfg.attr {
          buf.push_str(&phead_s.to_praline_attr());
          }
          if hint_term {
            buf.push_str("()");
          }
        }
        &Node_::Prefix(ref largs, ref rarg) => {
          //println!("DEBUG:  Geometry::_node_render_praline: Prefix unimpl: {:?}", node);
          // TODO TODO
          let mut its = false;
          if largs.len() == 1 {
            match &*largs[0] {
              &Node_::PHead(ref phead_s) => {
                if phead_s.as_raw_str() == "its" {
                  let rarg_s = self._node_render_praline(cfg, &**rarg.as_ref().ok_or(())?)?;
                  buf.push_str(&rarg_s);
                  its = true;
                  buf.push_str("(_\"");
                  buf.push_str(&phead_s.to_praline_str());
                  buf.push_str("\"_");
                  if cfg.attr {
                  buf.push_str(&phead_s.to_praline_attr());
                  }
                  buf.push_str(")");
                }
              }
              _ => {}
            }
          }
          if !its {
          let rarg_s = self._node_render_praline_(cfg, &**rarg.as_ref().ok_or(())?, true)?;
          buf.push_str(&rarg_s);
          if largs.len() > 0 {
            buf.push_str(" (with ");
          }
          for (k, larg) in largs.iter().enumerate() {
            if k > 0 {
              buf.push_str(" , ");
            }
            let larg_s = self._node_render_praline_(cfg, &**larg, true)?;
            buf.push_str(&larg_s);
          }
          if largs.len() > 0 {
            buf.push_str(" )");
          }
          }
        }
        &Node_::Pred(ref pred_s, ref larg, ref rarg, ref ctl_args) => {
          /*if pred_s.as_raw_str() == "distinct" {
            // FIXME FIXME
            break 'outer;
          }*/
          // FIXME: vectorization.
          let larg_s = self._node_render_praline_(cfg, &**larg.as_ref().ok_or(())?, true)?;
          buf.push_str("\"");
          buf.push_str(&pred_s.to_praline_str());
          buf.push_str("\"");
          if cfg.attr {
          buf.push_str(&pred_s.to_praline_attr());
          }
          buf.push_str("(");
          buf.push_str(&larg_s);
          if let Some(rarg) = rarg.as_ref() {
            buf.push_str(", ");
            let rarg_s = self._node_render_praline_(cfg, &**rarg, true)?;
            buf.push_str(&rarg_s);
          }
          // FIXME: semantics of (pred, ctl) cases.
          for ctl_kvarg in ctl_args.iter() {
            match &*ctl_kvarg.0 {
              &Node_::Ctl(ref ctl_s, ..) => {
                let ctl_kind = CtlKind::from(ctl_s.as_raw_str());
                match (pred_s.as_raw_str(), ctl_kind) {
                  ("meets", CtlKind::Again) |
                  ("meet", CtlKind::Again) => {
                    // TODO TODO
                  }
                  // FIXME: X "on" (e.g. "intersect on") is a special case.
                  ("lies", CtlKind::On) |
                  ("lie", CtlKind::On) => {
                    // FIXME: reset the pred to "on".
                    if let Some(ctl_varg) = ctl_kvarg.1.as_ref() {
                      buf.push_str(", ");
                      let ctl_varg_s = self._node_render_praline(cfg, &**ctl_varg)?;
                      buf.push_str(&ctl_varg_s);
                    }
                    buf.push_str(")");
                  }
                  _ => {
                    buf.push_str(")");
                    if let Some(ctl_varg) = ctl_kvarg.1.as_ref() {
                      buf.push_str(" -> ");
                      let ctl_varg_s = self._node_render_praline(cfg, &**ctl_varg)?;
                      buf.push_str(&ctl_varg_s);
                    }
                  }
                }
              }
              _ => return Err(())
            }
          }
        }
        &Node_::Unify(_, ref larg, ref rarg) => {
          // FIXME FIXME: compressed case logic.
          match (&**larg.as_ref().ok_or(())?, &**rarg.as_ref().ok_or(())?) {
            (&Node_::Name(..), &Node_::Head(..)) |
            (&Node_::Name(..), &Node_::Subst(..)) |
            (&Node_::Name(..), &Node_::Prefix(..)) |
            // FIXME: (Pair, _) cases yield double ':'.
            (&Node_::Pair(..), &Node_::Head(..)) |
            (&Node_::Pair(..), &Node_::Subst(..)) |
            (&Node_::Pair(..), &Node_::Prefix(..)) |
            (&Node_::Mult(..), &Node_::Head(..)) |
            (&Node_::Mult(..), &Node_::Subst(..)) |
            (&Node_::Mult(..), &Node_::Prefix(..)) => {
              let larg_s = self._node_render_praline(cfg, &**larg.as_ref().ok_or(())?)?;
              let rarg_s = self._node_render_praline_(cfg, &**rarg.as_ref().ok_or(())?, true)?;
              /*buf.push_str(&larg_s);
              buf.push_str(": ");
              buf.push_str(&rarg_s);*/
              buf.push_str(&rarg_s);
              buf.push_str(" -> ");
              buf.push_str(&larg_s);
            }
            // FIXME FIXME: missing cases.
            (&Node_::Prefix(ref pre_largs, ref pre_rarg), &Node_::Name(..)) => {
              // TODO TODO
              let mut its = false;
              if pre_largs.len() == 1 {
                match &*pre_largs[0] {
                  &Node_::PHead(ref phead_s) => {
                    if phead_s.as_raw_str() == "its" {
                      its = true;
                      let pre_rarg_s = self._node_render_praline(cfg, &**pre_rarg.as_ref().ok_or(())?)?;
                      let rarg_s = self._node_render_praline(cfg, &**rarg.as_ref().ok_or(())?)?;
                      buf.push_str(&pre_rarg_s);
                      buf.push_str("(_\"");
                      buf.push_str(&phead_s.to_praline_str());
                      buf.push_str("\"_");
                      if cfg.attr {
                      buf.push_str(&phead_s.to_praline_attr());
                      }
                      buf.push_str(")");
                      buf.push_str(" -> ");
                      buf.push_str(&rarg_s);
                    }
                  }
                  _ => {}
                }
              }
              if !its {
              let larg_s = self._node_render_praline_(cfg, &**larg.as_ref().ok_or(())?, true)?;
              let rarg_s = self._node_render_praline(cfg, &**rarg.as_ref().ok_or(())?)?;
              buf.push_str(&larg_s);
              buf.push_str(" -> ");
              buf.push_str(&rarg_s);
              }
            }
            (&Node_::Name(..), &Node_::PHead(..)) |
            (&Node_::Pair(..), &Node_::PHead(..)) |
            (&Node_::Mult(..), &Node_::PHead(..)) => {
              let larg_s = self._node_render_praline_(cfg, &**larg.as_ref().ok_or(())?, true)?;
              let rarg_s = self._node_render_praline(cfg, &**rarg.as_ref().ok_or(())?)?;
              buf.push_str(&rarg_s);
              buf.push_str("(");
              buf.push_str(&larg_s);
              buf.push_str(")");
            }
            (&Node_::Name(..), &Node_::Apply(..)) |
            (&Node_::Pair(..), &Node_::Apply(..)) |
            // FIXME: vectorize Mult.
            (&Node_::Mult(..), &Node_::Apply(..)) => {
              let larg_s = self._node_render_praline(cfg, &**larg.as_ref().ok_or(())?)?;
              let rarg_s = self._node_render_praline_(cfg, &**rarg.as_ref().ok_or(())?, true)?;
              buf.push_str(&rarg_s);
              buf.push_str(" -> ");
              buf.push_str(&larg_s);
            }
            (&Node_::Mult(ref l_rev_args), &Node_::Mult(ref _r_rev_args)) => {
              if let Some(&(_, ref llarg)) = l_rev_args.iter().next() {
                //if let Some(&(_, ref rrarg)) = r_rev_args.iter().next() {
                  match &**llarg {
                    &Node_::Name(..) => {
                      let larg_s = self._node_render_praline(cfg, &**larg.as_ref().ok_or(())?)?;
                      let rarg_s = self._node_render_praline_(cfg, &**rarg.as_ref().ok_or(())?, true)?;
                      buf.push_str(&rarg_s);
                      buf.push_str(" -> ");
                      buf.push_str(&larg_s);
                    }
                    _ => {
                      println!("DEBUG:  Geometry::_node_render_praline: Unify unimpl: non-Name Mult Mult");
                    }
                  }
                //}
              }
            }
            (&Node_::Apply(..), &Node_::Name(..)) |
            (&Node_::Apply(..), &Node_::Pair(..)) |
            // FIXME: vectorize Mult.
            (&Node_::Apply(..), &Node_::Mult(..)) => {
              let larg_s = self._node_render_praline_(cfg, &**larg.as_ref().ok_or(())?, true)?;
              let rarg_s = self._node_render_praline(cfg, &**rarg.as_ref().ok_or(())?)?;
              buf.push_str(&larg_s);
              buf.push_str(" -> ");
              buf.push_str(&rarg_s);
            }
            _ => {
              println!("DEBUG:  Geometry::_node_render_praline: Unify unimpl: {:?}", node);
            }
          }
        }
        &Node_::Arg0(ref arg0_s, ref arg) => {
          match arg0_s.as_raw_str() {
            "Prove" | "prove" => {
              let arg_s = self._node_render_praline(cfg, &**arg.as_ref().ok_or(())?)?;
              buf.push_str("prove ( ");
              buf.push_str(&arg_s);
              buf.push_str(" )");
            }
            _ => {
              println!("DEBUG:  Geometry::_node_render_praline: Arg0 unimpl: {:?}", node);
            }
          }
        }
        _ => {
          println!("DEBUG:  Geometry::_node_render_praline: outer unimpl: {:?}", node);
        }
      }
      break 'outer;
    } // 'outer
    Ok(buf.into())
  }

  pub fn _render_praline(&self) -> Result<SmolStr, ()> {
    self._render_praline_(RenderConfig::default())
  }

  pub fn _render_praline_(&self, cfg: RenderConfig) -> Result<SmolStr, ()> {
    // TODO: config.
    let mut buf = String::new();
    for &(root, _) in self.tree_.rootstop.iter() {
      let root_node = match self.nodes.get(&root) {
        None => return Err(()),
        Some(inode) => {
          if inode.node.is_none() {
            return Err(());
          }
          inode.node.clone().unwrap()
        }
      };
      let s = self._node_render_praline(cfg, &*root_node)?;
      buf.push_str(" ");
      buf.push_str(&s);
      buf.push_str(".");
      // TODO TODO
    }
    Ok(buf.into())
  }

  pub fn _node_init(&mut self, i: ItemNum, item: &Item_, reinit: bool) -> Node_ {
    // TODO TODO
    match &mut self.mode {
      &mut DrawMode::Replay{ref mut log} => {
        log.tracebuf.push(TraceEntry::NodeInit_(i, item.kind(), reinit).into());
      }
      _ => {
        unimplemented!();
      }
    }
    if self.trace {
    println!("DEBUG:  _node_init:  i={:?} item={:?}", i, item);
    }
    match item {
      &Item_::Name_(ref name_s, name_x, ..) => {
        Node_::Name(name_s.clone(), name_x)
      }
      &Item_::Head_(ref head_s, ref quant, ..) => {
        Node_::Head(head_s.clone(), quant.clone(), Vec::new())
      }
      &Item_::Unify_(ref unify_s, ..) => {
        Node_::Unify(unify_s.clone(), None, None)
      }
      &Item_::PHead_(ref pred_s, ..) => {
        Node_::PHead(pred_s.clone())
      }
      &Item_::Pred_(ref pred_s, ..) => {
        Node_::Pred(pred_s.clone(), None, None, Vec::new())
      }
      &Item_::Arg0_(ref arg0_s, ..) => {
        Node_::Arg0(arg0_s.clone(), None)
      }
      &Item_::Ctl_(ref ctl_s, ..) => {
        Node_::Ctl(ctl_s.clone())
      }
      _ => {
        println!("DEBUG:  _node_init: item={:?}", item);
        //self._debug_dump();
        unimplemented!();
      }
    }
  }

  pub fn _node_apply(&mut self, curkey: ItemNum, cur_node: &mut Node_, /*link: Link_,*/ argkey: ItemNum, arg_node: &Node_, depth: i32) -> Result<(), Err_> {
  //pub fn _node_apply(&self, curkey: ItemNum, cur_node: &mut Node_, /*link: Link_,*/ argkey: ItemNum, arg_node: &mut Node_, depth: i32) -> Result<(), Err_> {}
    // TODO TODO
    match &mut self.mode {
      &mut DrawMode::Replay{ref mut log} => {
        log.tracebuf.push(TraceEntry::NodeApply(curkey, cur_node.kind(), argkey, arg_node.kind()).into());
      }
      _ => {
        unimplemented!();
      }
    }
    if self.trace {
    println!("DEBUG:  _node_apply: cur={:?} {:?} arg={:?} {:?} depth={}", curkey, cur_node, argkey, arg_node, depth);
    }
    match cur_node {
      &mut Node_::Name(..) => {
        match arg_node {
          &Node_::Mult(ref rev_args) => {
            for &(_, ref arg) in rev_args.iter() {
              match &**arg {
                &Node_::Name(..) |
                &Node_::Head(..) => {}
                // FIXME: Pair.
                _ => {
                  return e_bot();
                }
              }
            }
            let mut rev_args = rev_args.clone();
            rev_args.push((None, cur_node.clone().into()));
            *cur_node = Node_::Mult(rev_args);
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Name <-- Mult");
            }
            return Ok(());
          }
          &Node_::Unify(ref unify_s, ref larg, ref rarg) => {
            if larg.is_some() {
              return e_bot();
            }
            let new_larg = cur_node.clone().into();
            *cur_node = Node_::Unify(unify_s.clone(), Some(new_larg), rarg.clone());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Name <-- Unify");
            }
            return Ok(());
          }
          &Node_::Pred(ref pred_s, ref larg, ref rarg, ref ctl_args) => {
            if larg.is_some() {
              return e_bot();
            }
            let new_larg = cur_node.clone().into();
            *cur_node = Node_::Pred(pred_s.clone(), Some(new_larg), rarg.clone(), ctl_args.clone());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Name <-- Pred");
            }
            return Ok(());
          }
          _ => {
            e_top()
          }
        }
      }
      &mut Node_::Head(_, ref head_q, ..) => {
        match arg_node {
          &Node_::Name(..) => {
            let lhs_node = cur_node.clone().into();
            let rhs_node = arg_node.clone().into();
            *cur_node = Node_::Pair(Some(lhs_node), Some(rhs_node));
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Head <-- Pair");
            }
            return Ok(());
          }
          &Node_::Apply(ref apply_s, ref larg, ref rarg, ref ctl_args) => {
            if larg.is_some() {
              return e_bot();
            }
            let new_larg = cur_node.clone().into();
            *cur_node = Node_::Apply(apply_s.clone(), Some(new_larg), rarg.clone(), ctl_args.clone());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Head <-- Apply");
            }
            return Ok(());
          }
          &Node_::Subst(ref subst_s, ref larg, ref rarg) => {
            if larg.is_some() {
              return e_bot();
            }
            let new_larg = cur_node.clone().into();
            *cur_node = Node_::Subst(subst_s.clone(), Some(new_larg), rarg.clone());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Head <-- Subst");
            }
            return Ok(());
          }
          &Node_::Mult(ref rev_args) => {
            match head_q {
              /*&HeadQuant_::One => {
                if rev_args.len() >= 1 {
                  let mut rev_args = rev_args.clone();
                  rev_args.push((None, cur_node.clone().into()));
                  *cur_node = Node_::Mult(rev_args);
                  if self.trace {
                  println!("DEBUG:  _node_apply:   ok: Head (One) <-- Mult");
                  }
                  return Ok(());
                }
              }*/
              &HeadQuant_::One => {
                for &(_, ref rarg) in rev_args.iter().rev() {
                  match &**rarg {
                    // FIXME: allowing Name below misparses i=72.
                    /*&Node_::Name(..) |*/
                    &Node_::Head(..) |
                    &Node_::Pair(..) |
                    &Node_::Apply(..) |
                    &Node_::Subst(..) => {}
                    _ => {
                      return e_bot();
                    }
                  }
                }
                let mut rev_args = rev_args.clone();
                rev_args.push((None, cur_node.clone().into()));
                *cur_node = Node_::Mult(rev_args);
                if self.trace {
                println!("DEBUG:  _node_apply:   ok: Head (One) <-- Mult");
                }
                return Ok(());
              }
              &HeadQuant_::MultAnon |
              &HeadQuant_::Mult(_) => {
                // FIXME: missing condition.
                let lhs_node = cur_node.clone().into();
                let rhs_node = arg_node.clone().into();
                *cur_node = Node_::Pair(Some(lhs_node), Some(rhs_node));
                if self.trace {
                println!("DEBUG:  _node_apply:   ok: Head (Mult) <-- Pair (Mult)");
                }
                return Ok(());
              }
              _ => {
                e_top()
              }
            }
          }
          &Node_::Pred(ref pred_s, ref larg, ref rarg, ref ctl_args) => {
            // TODO TODO
            if larg.is_some() {
              return e_bot();
            }
            let new_larg = cur_node.clone().into();
            *cur_node = Node_::Pred(pred_s.clone(), Some(new_larg), rarg.clone(), ctl_args.clone());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Head <-- Pred");
            }
            return Ok(());
          }
          _ => {
            e_top()
          }
        }
      }
      &mut Node_::Apply(..) => {
        match arg_node {
          // TODO TODO
          &Node_::Unify(ref unify_s, ref larg, ref rarg) => {
            match unify_s.as_raw_str() {
              "is" => {
                return e_bot();
              }
              _ => {}
            }
            if larg.is_some() {
              return e_bot();
            }
            let new_larg = cur_node.clone().into();
            *cur_node = Node_::Unify(unify_s.clone(), Some(new_larg), rarg.clone());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Apply <-- Unify");
            }
            return Ok(());
          }
          &Node_::Pred(ref pred_s, ref larg, ref rarg, ref ctl_args) => {
            if larg.is_some() {
              return e_bot();
            }
            let new_larg = cur_node.clone().into();
            *cur_node = Node_::Pred(pred_s.clone(), Some(new_larg), rarg.clone(), ctl_args.clone());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Apply <-- Pred");
            }
            return Ok(());
          }
          _ => {
            e_top()
          }
        }
      }
      &mut Node_::Subst(.., ref mut l_rarg) => {
        match arg_node {
          &Node_::Mult(ref r_rev_args) => {
            // FIXME FIXME
            if l_rarg.is_none() {
              return e_bot();
            }
            // FIXME: should be compat w/ r_rev_args.
            /*for &(_, ref arg) in rev_args.iter() {
              match &**arg {
                &Node_::Name(..) |
                &Node_::Head(..) |
                &Node_::Pair(..) => {}
                _ => {
                  return e_bot();
                }
              }
            }*/
            match &**l_rarg.as_ref().unwrap() {
              &Node_::Name(..) |
              &Node_::Head(..) |
              &Node_::Pair(..) => {}
              // FIXME
              /*&Node_::Mult(..) => {
              }*/
              _ => {
                return e_bot();
              }
            }
            let mut rev_args = r_rev_args.clone();
            rev_args.push((None, l_rarg.clone().unwrap()));
            *l_rarg = Some(Node_::Mult(rev_args).into());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Subst <-- Mult");
            }
            return Ok(());
          }
          _ => {
            e_top()
          }
        }
      }
      &mut Node_::Pair(..) => {
        match arg_node {
          // TODO TODO
          &Node_::Mult(ref rev_args) => {
            for &(_, ref arg) in rev_args.iter() {
              match &**arg {
                &Node_::Name(..) |
                &Node_::Head(..) |
                &Node_::Pair(..) => {}
                _ => {
                  return e_bot();
                }
              }
            }
            let mut rev_args = rev_args.clone();
            rev_args.push((None, cur_node.clone().into()));
            *cur_node = Node_::Mult(rev_args);
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Pair <-- Mult");
            }
            return Ok(());
          }
          &Node_::Unify(ref unify_s, ref larg, ref rarg) => {
            if larg.is_some() {
              return e_bot();
            }
            let new_larg = cur_node.clone().into();
            *cur_node = Node_::Unify(unify_s.clone(), Some(new_larg), rarg.clone());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Pair <-- Unify");
            }
            return Ok(());
          }
          &Node_::Pred(ref pred_s, ref larg, ref rarg, ref ctl_args) => {
            if larg.is_some() {
              return e_bot();
            }
            let new_larg = cur_node.clone().into();
            *cur_node = Node_::Pred(pred_s.clone(), Some(new_larg), rarg.clone(), ctl_args.clone());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Pair <-- Pred");
            }
            return Ok(());
          }
          _ => {
            e_top()
          }
        }
      }
      &mut Node_::Mult(ref l_rev_args) => {
        match arg_node {
          // TODO TODO
          &Node_::Mult(ref r_rev_args) => {
            // FIXME FIXME
            /*for &(_, ref arg) in rev_args.iter() {
              match &**arg {
                &Node_::Name(..) |
                &Node_::Head(..) |
                &Node_::Pair(..) => {}
                _ => {
                  return e_bot();
                }
              }
            }*/
            let mut rev_args = r_rev_args.clone();
            rev_args.extend_from_slice(l_rev_args);
            *cur_node = Node_::Mult(rev_args);
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Mult <-- Mult");
            }
            return Ok(());
          }
          &Node_::Unify(ref unify_s, ref larg, ref rarg) => {
            match unify_s.as_raw_str() {
              "is" => {
                return e_bot();
              }
              _ => {}
            }
            if larg.is_some() {
              return e_bot();
            }
            let new_larg = cur_node.clone().into();
            *cur_node = Node_::Unify(unify_s.clone(), Some(new_larg), rarg.clone());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Mult <-- Unify");
            }
            return Ok(());
          }
          &Node_::Pred(ref pred_s, ref larg, ref rarg, ref ctl_args) => {
            if larg.is_some() {
              return e_bot();
            }
            let new_larg = cur_node.clone().into();
            *cur_node = Node_::Pred(pred_s.clone(), Some(new_larg), rarg.clone(), ctl_args.clone());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Mult <-- Pred");
            }
            return Ok(());
          }
          _ => {
            e_top()
          }
        }
      }
      &mut Node_::PHead(..) => {
        match arg_node {
          // TODO TODO
          /*&Node_::Name(..) => {
            let lhs_node = cur_node.clone().into();
            let rhs_node = arg_node.clone().into();
            *cur_node = Node_::Pair(Some(lhs_node), Some(rhs_node));
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: PHead <-- Pair (Name)");
            }
            return Ok(());
          }*/
          &Node_::Head(..) |
          &Node_::Pair(..) => {
            let lhs_node = cur_node.clone().into();
            let rhs_node = arg_node.clone().into();
            *cur_node = Node_::Prefix(vec![lhs_node], Some(rhs_node));
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: PHead <-- Head | Pair");
            }
            return Ok(());
          }
          &Node_::Subst(ref subst_s, ref larg, ref rarg) => {
            //println!("DEBUG:  _node_apply:   PHead <-- Subst: cur={:?} arg={:?}", cur_node, arg_node);
            if larg.is_none() {
              return e_bot();
            }
            let lhs_node = cur_node.clone().into();
            let new_larg = Node_::Prefix(vec![lhs_node], larg.clone()).into();
            *cur_node = Node_::Subst(subst_s.clone(), Some(new_larg), rarg.clone());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: PHead <-- Subst");
            }
            return Ok(());
          }
          &Node_::PHead(..) => {
            let lhs_node = cur_node.clone().into();
            let rhs_node = arg_node.clone().into();
            *cur_node = Node_::Prefix(vec![lhs_node, rhs_node], None);
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: PHead <-- PHead");
            }
            return Ok(());
          }
          &Node_::Prefix(ref r_pre_args, ref post_arg) => {
            let mut pre_args = Vec::new();
            pre_args.push(cur_node.clone().into());
            pre_args.extend_from_slice(r_pre_args);
            *cur_node = Node_::Prefix(pre_args, post_arg.clone());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: PHead <-- Prefix");
            }
            return Ok(());
          }
          _ => {
            e_top()
          }
        }
      }
      &mut Node_::Prefix(ref mut pre_args, ref mut post_arg) => {
        match arg_node {
          // TODO TODO
          &Node_::Name(..) => {
            // FIXME FIXME
            if post_arg.is_none() {
              return e_bot();
            }
            let lhs_node = cur_node.clone().into();
            let rhs_node = arg_node.clone().into();
            *cur_node = Node_::Pair(Some(lhs_node), Some(rhs_node));
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Prefix <-- Pair (Name)");
            }
            return Ok(());
          }
          &Node_::Head(..) |
          &Node_::Pair(..) => {
            if post_arg.is_some() {
              return e_bot();
            }
            *post_arg = Some(arg_node.clone().into());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Prefix <-- Head | Pair");
            }
            return Ok(());
          }
          &Node_::PHead(..) => {
            // NB: arg check is essentially a guard.
            if post_arg.is_some() {
              return e_bot();
            }
            pre_args.push(arg_node.clone().into());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Prefix <-- PHead");
            }
            return Ok(());
          }
          &Node_::Unify(ref unify_s, ref larg, ref rarg) => {
            if larg.is_some() {
              return e_bot();
            }
            let new_larg = cur_node.clone().into();
            *cur_node = Node_::Unify(unify_s.clone(), Some(new_larg), rarg.clone());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Prefix <-- Unify");
            }
            return Ok(());
          }
          &Node_::Pred(ref pred_s, ref larg, ref rarg, ref ctl_args) => {
            if larg.is_some() {
              return e_bot();
            }
            let new_larg = cur_node.clone().into();
            *cur_node = Node_::Pred(pred_s.clone(), Some(new_larg), rarg.clone(), ctl_args.clone());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Prefix <-- Pred");
            }
            return Ok(());
          }
          _ => {
            e_top()
          }
        }
      }
      &mut Node_::Unify(ref _unify_s, ref _larg, ref mut rarg) => {
        match arg_node {
          // TODO TODO
          &Node_::Name(..) |
          &Node_::Head(..) |
          &Node_::Pair(..) |
          &Node_::Apply(..) |
          &Node_::Subst(..) |
          &Node_::Mult(..) |
          &Node_::PHead(..) |
          &Node_::Prefix(..) => {
            // FIXME FIXME: check arg args.
            if rarg.is_some() {
              return e_bot();
            }
            let new_rarg = arg_node.clone().into();
            *rarg = Some(new_rarg);
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Unify <-- Name | Head");
            }
            return Ok(());
          }
          _ => {
            e_top()
          }
        }
      }
      &mut Node_::Pred(ref pred_s, ref _larg, ref mut rarg, ref mut ctl_args) => {
        match arg_node {
          // TODO TODO
          &Node_::Name(..) |
          &Node_::Head(..) |
          &Node_::Pair(..) => {
            // FIXME FIXME: check arg args.
            if rarg.is_some() {
              return e_bot();
            }
            *rarg = Some(arg_node.clone().into());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Pred <-- Name | Head");
            }
            return Ok(());
          }
          /*&Node_::Mult(ref rev_args) => {
            // FIXME FIXME: instead prefer MultPair or similar.
            /*if rev_args.len() == 1 {
              let lhs_node = cur_node.clone().into();
              let mut pseq_args = vec![lhs_node];
              pseq_args.push(rev_args[0].1.clone());
              *cur_node = Node_::PSeq(pseq_args);
              return Ok(());
            }*/
          }*/
          &Node_::Ctl(ref ctl_s, ..) => {
            let ctl_kind = CtlKind::from(ctl_s.as_raw_str());
            match (pred_s.as_raw_str(), ctl_kind) {
              ("meets", CtlKind::Again) |
              ("meet", CtlKind::Again) => {
                ctl_args.push((arg_node.clone().into(), None));
                if self.trace {
                println!("DEBUG:  _node_apply:   ok: Pred <-- Pred (Ctl)");
                }
                return Ok(());
              }
              _ => {
                e_top()
              }
            }
          }
          &Node_::CtlPair(ref ctl, ref arg) => {
            let ctl_kind = match &**ctl {
              &Node_::Ctl(ref ctl_s, ..) => {
                CtlKind::from(ctl_s.as_raw_str())
              }
              _ => panic!("bug")
            };
            match (pred_s.as_raw_str(), ctl_kind) {
              // TODO TODO
              ("meets", CtlKind::At) |
              ("meet", CtlKind::At) |
              //("meet", CtlKind::In) |
              ("meets", CtlKind::On) |
              ("meet", CtlKind::On) |
              ("intersects", CtlKind::At) |
              ("intersects", CtlKind::In) |
              ("intersects", CtlKind::On) |
              ("intersect", CtlKind::At) |
              ("intersect", CtlKind::In) |
              ("intersect", CtlKind::On) |
              ("lies", CtlKind::On) |
              ("lie", CtlKind::On) |
              ("passes", CtlKind::Through) |
              ("pass", CtlKind::Through) => {
                ctl_args.push((ctl.clone(), arg.clone().into()));
                if self.trace {
                println!("DEBUG:  _node_apply:   ok: Pred <-- Pred (CtlPair)");
                }
                return Ok(());
              }
              _ => {
                e_top()
              }
            }
          }
          _ => {
            e_top()
          }
        }
      }
      /*&mut Node_::PSeq(ref mut pseq_args) => {
        // TODO TODO
        match pseq_args.last_mut() {
          None => {
            return e_bot()
          }
          Some(node) => {
            return self._node_apply(curkey, Rc::make_mut(node), argkey, arg_node, depth + 1);
          }
        }
      }*/
      &mut Node_::Arg0(ref _arg0_s, ref mut inner_arg) => {
        match arg_node {
          // TODO TODO
          &Node_::Name(..) |
          &Node_::Head(..) |
          &Node_::Pair(..) |
          &Node_::Apply(..) |
          &Node_::Subst(..) |
          &Node_::Mult(..) |
          &Node_::PHead(..) |
          &Node_::Prefix(..) |
          &Node_::Pred(..) |
          &Node_::Unify(..) => {
            // FIXME FIXME: check arg args.
            if inner_arg.is_some() {
              return e_bot();
            }
            *inner_arg = Some(arg_node.clone().into());
            if self.trace {
            println!("DEBUG:  _node_apply:   ok: Arg0 <-- _");
            }
            return Ok(());
          }
          _ => {
            e_top()
          }
        }
      }
      &mut Node_::Ctl(ref ctl_s) => {
        let ctl_kind = CtlKind::from(ctl_s.as_raw_str());
        // FIXME: not all combos are meaningful.
        match arg_node {
          &Node_::Head(..) |
          &Node_::Pair(..) |
          &Node_::PHead(..) |
          &Node_::Prefix(..) => {
            match ctl_kind {
              CtlKind::With => {
                // FIXME FIXME: prefer CtlPair.
                let new_rarg = arg_node.clone().into();
                *cur_node = Node_::Subst(ctl_s.clone(), None, Some(new_rarg));
                /*
                let lhs_node = cur_node.clone().into();
                let rhs_node = arg_node.clone().into();
                *cur_node = Node_::CtlPair(lhs_node, rhs_node);
                */
                if self.trace {
                println!("DEBUG:  _node_apply:   ok: Ctl <-- Subst");
                }
                return Ok(());
              }
              _ => {}
            }
          }
          _ => {}
        }
        match arg_node {
          &Node_::Name(..) |
          &Node_::Head(..) |
          &Node_::Pair(..) |
          &Node_::Apply(..) |
          &Node_::Subst(..) |
          &Node_::Mult(..) |
          // FIXME: PHead should also belong here, but must be partial;
          // this case motivates mut arg (PHead to Prefix promotion).
          &Node_::PHead(..) |
          &Node_::Prefix(..) => {
            match ctl_kind {
              CtlKind::Of => {
                // FIXME FIXME: prefer CtlPair.
                let new_rarg = arg_node.clone().into();
                *cur_node = Node_::Apply(ctl_s.clone(), None, Some(new_rarg), Vec::new());
                /*
                let lhs_node = cur_node.clone().into();
                let rhs_node = arg_node.clone().into();
                *cur_node = Node_::CtlPair(lhs_node, rhs_node);
                */
                if self.trace {
                println!("DEBUG:  _node_apply:   ok: Ctl <-- Apply");
                }
                return Ok(());
              }
              CtlKind::At |
              CtlKind::In |
              CtlKind::On => {
                let lhs_node = cur_node.clone().into();
                let rhs_node = arg_node.clone().into();
                *cur_node = Node_::CtlPair(lhs_node, rhs_node);
                if self.trace {
                println!("DEBUG:  _node_apply:   ok: Ctl <-- CtlPair");
                }
                return Ok(());
              }
              _ => {}
            }
          }
          _ => {}
        }
        match arg_node {
          &Node_::Unify(..) |
          &Node_::Pred(..) => {
            match ctl_kind {
              CtlKind::Whose => {
                // FIXME FIXME: prefer CtlPair.
                let new_rarg = arg_node.clone().into();
                *cur_node = Node_::Subst(ctl_s.clone(), None, Some(new_rarg));
                if self.trace {
                println!("DEBUG:  _node_apply:   ok: Ctl <-- Subst");
                }
                return Ok(());
              }
              _ => {}
            }
          }
          _ => {}
        }
        match arg_node {
          &Node_::Name(..) |
          &Node_::Head(..) |
          &Node_::Pair(..) |
          &Node_::Apply(..) |
          &Node_::Subst(..) |
          &Node_::PHead(..) |
          &Node_::Prefix(..) => {
            match ctl_kind {
              CtlKind::Comma |
              CtlKind::And |
              CtlKind::CommaAnd => {
                // FIXME FIXME: prefer CtlPair.
                let lhs_node = cur_node.clone().into();
                let rhs_node = arg_node.clone().into();
                *cur_node = Node_::Mult(vec![(Some(lhs_node), rhs_node)]);
                return Ok(());
              }
              _ => {}
            }
          }
          _ => {}
        }
        e_top()
      }
      _ => {
        e_top()
      }
    }
    //e_top()
  }

  pub fn _recompile(&mut self, i: ItemNum) -> Result<(), Err_> {
    // TODO TODO
    match &mut self.mode {
      &mut DrawMode::Replay{ref mut log} => {
        log.tracebuf.push(TraceEntry::Recompile(i).into());
      }
      _ => {
        unimplemented!();
      }
    }
    if self.trace {
    println!("DEBUG:  _recompile:  i={:?}", i);
    }
    self.tree_.recomp.clear();
    let mut curkey = i;
    loop {
      self.tree_.recomp.insert(curkey);
      let cur_item = match self.items.get(&curkey) {
        None => {
          return e_bot();
        }
        Some(item) => item.clone()
      };
      if self.trace {
      println!("DEBUG:  _recompile:    curkey={:?} cur item={:?} rc={:?}", curkey, cur_item, self.tree_.recomp);
      }
      let mut retry = false;
      'retry: loop {
        if self.trace {
        println!("DEBUG:  _recompile:      retry? {:?}", retry);
        }
        match self.nodes.get(&curkey) {
          None => {
            let cur_node = self._node_init(curkey, &cur_item, retry);
            assert!(self.nodes.insert(curkey, INode_::new(curkey, cur_node)).is_none());
            if self.trace {
            println!("DEBUG:  _recompile:      init");
            }
          }
          _ => {}
        }
        match self.nodes.get(&curkey) {
          None => panic!("bug"),
          Some(cur_inode) => {
            let cur_comp = match &cur_item {
              // TODO TODO
              &Item_::Name_(.., ref vargs) |
              &Item_::Head_(.., ref vargs) |
              &Item_::PHead_(.., ref vargs) |
              &Item_::Unify_(.., ref vargs) |
              &Item_::Pred_(.., ref vargs) |
              &Item_::Arg0_(.., ref vargs) => {
                vargs.last().map(|&i| i)
              }
              &Item_::Ctl_(.., arg) => {
                arg
              }
              // TODO TODO
              _ => None
              //_ => unimplemented!()
            }.unwrap_or(curkey);
            // FIXME: the diff logic below is wrong/incomplete.
            if cur_inode.ub > cur_comp {
              // FIXME FIXME
              if self.trace {
              println!("DEBUG:  _recompile:    err: cur inode.ub={:?} cur ub={:?}", cur_inode.ub, cur_comp);
              }
              //panic!("bug");
              return e_bot();
            /*} else if cur_inode.ub == cur_comp {
              // FIXME FIXME
              //panic!("bug");
              // TODO TODO: can this ever not bot?
              return e_bot();*/
            } else /*if cur_inode.ub <= cur_comp */{
              let mut cur_inode = replace(self.nodes.get_mut(&curkey).unwrap(), INode_::top());
              if self.trace {
              println!("DEBUG:  _recompile:      pre:  cur inode.ub={:?} cur ub={:?}", cur_inode.ub, cur_comp);
              println!("DEBUG:  _recompile:      pre:  cur node={:?}", cur_inode.node);
              }
              let mut apply = retry || cur_inode.ub == curkey;
              if self.trace {
              println!("DEBUG:  _recompile:      apply? {:?}", apply);
              }
              match &cur_item {
                // TODO TODO
                &Item_::Name_(.., ref vargs) |
                &Item_::Head_(.., ref vargs) |
                &Item_::PHead_(.., ref vargs) |
                &Item_::Unify_(.., ref vargs) |
                &Item_::Pred_(.., ref vargs) |
                &Item_::Arg0_(.., ref vargs) => {
                  for &arg in vargs.iter() {
                    if self.trace {
                    println!("DEBUG:  _recompile:      arg={:?} apply? {:?}", arg, apply);
                    }
                    if !apply {
                      if !retry && self.tree_.recomp.contains(&arg) {
                        if self.trace {
                        println!("DEBUG:  _recompile:      retry");
                        }
                        let _ = self.nodes.remove(&curkey);
                        retry = true;
                        continue 'retry;
                      }
                      if cur_inode.ub == arg {
                        apply = true;
                      }
                      continue;
                    }
                    match self.nodes.get(&arg) {
                      None => {
                        return e_bot();
                      }
                      Some(_) => {}
                    }
                      //Some(arg_inode) => {
                    let arg_inode = replace(self.nodes.get_mut(&arg).unwrap(), INode_::top());
                        self._node_apply(
                            curkey,
                            Rc::make_mut(&mut cur_inode.node.as_mut().unwrap()),
                            arg,
                            // FIXME FIXME: mut arg for PHead -> Prefix promotion.
                            arg_inode.node.as_ref().unwrap(),
                            //Rc::make_mut(&mut arg_inode.node.as_mut().unwrap()),
                            0
                        )?;
                        cur_inode.ub = arg;
                    let _ = replace(self.nodes.get_mut(&arg).unwrap(), arg_inode);
                      //}
                    //}
                  }
                }
                &Item_::Ctl_(.., arg) => {
                  if let Some(arg) = arg {
                    if self.trace {
                    println!("DEBUG:  _recompile:      arg={:?} apply? {:?}", arg, apply);
                    }
                    if !apply {
                      if !retry && self.tree_.recomp.contains(&arg) {
                        if self.trace {
                        println!("DEBUG:  _recompile:      retry");
                        }
                        let _ = self.nodes.remove(&curkey);
                        retry = true;
                        continue 'retry;
                      }
                      if cur_inode.ub == arg {
                        apply = true;
                      }
                      continue;
                    }
                    match self.nodes.get(&arg) {
                      None => {
                        return e_bot();
                      }
                      Some(_) => {}
                    }
                      //Some(arg_inode) => {
                    let arg_inode = replace(self.nodes.get_mut(&arg).unwrap(), INode_::top());
                        self._node_apply(
                            curkey,
                            Rc::make_mut(&mut cur_inode.node.as_mut().unwrap()),
                            arg,
                            // FIXME FIXME: mut arg for PHead -> Prefix promotion.
                            arg_inode.node.as_ref().unwrap(),
                            //Rc::make_mut(&mut arg_inode.node.as_mut().unwrap()),
                            0
                        )?;
                        cur_inode.ub = arg;
                    let _ = replace(self.nodes.get_mut(&arg).unwrap(), arg_inode);
                      //}
                    //}
                  }
                }
                // TODO TODO
                _ => {
                }
              }
              if self.trace {
              println!("DEBUG:  _recompile:      post: cur inode.ub={:?} cur ub={:?}", cur_inode.ub, cur_comp);
              println!("DEBUG:  _recompile:      post: cur node={:?}", cur_inode.node);
              }
              let _ = replace(self.nodes.get_mut(&curkey).unwrap(), cur_inode);
            }
          }
        }
        break; // 'retry
      }
      match self.tree_.jux.get(&curkey) {
        Some(&supkey) => {
          curkey = supkey;
          continue;
        }
        None => {}
      }
      match self.tree_.sup.get(&curkey) {
        Some(&supkey) => {
          curkey = supkey;
          continue;
        }
        None => {}
      }
      break;
    }
    // TODO TODO
    Ok(())
  }

  pub fn _get_item(&self, i: ItemNum) -> Result<&Item_, ()> {
    /*for idx in 0 .. self.items.len() {
      let item = self.items[idx].as_ref().unwrap();*/
    /*for item in self.items.iter() {
      if i == *item.0 {
        return Ok(&item.1);
      }
    }*/
    match self.items.get(&i) {
      Some(item) => {
        return Ok(item);
      }
      None => {}
    }
    Err(())
  }

  pub fn _cur_items_len(&self) -> usize {
    let mut ct = 0;
    for (_, item) in self.items.iter().rev() {
      match item {
        //&Item_::Stop |
        &Item_::Stop_(_) => {
          break;
        }
        _ => {}
      }
      ct += 1;
    }
    ct
  }

  pub fn _fresh_item_num(&mut self) -> ItemNum {
    let x = self.itemctr + 1;
    assert!(x > 0);
    self.itemctr = x;
    ItemNum(x)
  }

  pub fn _stage_item(&mut self, item: Item_) -> Result<(), Err_> {
    if self.stage.len() > 0 {
      // FIXME
      //unimplemented!();
      return e_bot();
    }
    let i = self._fresh_item_num();
    self.stage.push((i, item));
    Ok(())
  }

  pub fn _push_item_(&mut self, item: Item_) -> Result<(), Err_> {
    if self.stage.len() > 1 {
      // FIXME
      //unimplemented!();
      return e_bot();
    }
    let i = self._fresh_item_num();
    if self.stage.len() == 1 {
      let popitem = self.stage.pop().unwrap();
      self.prevstage.push(popitem.clone());
      self._reduce_item2(popitem, (i, item))
    } else /*if self.stage.len() <= 0 */{
      self._reduce_item_((i, item))
    }
  }

  pub fn _link_sup2(&mut self, li: ItemNum, ri0: ItemNum, ritem0: Item_, ri: ItemNum, ritem: Item_) -> Result<(), Err_> {
    let lkind = match self.items.get(&li) {
      None => panic!("bug"),
      Some(litem) => litem.kind()
    };
    match &mut self.mode {
      &mut DrawMode::Replay{ref mut log} => {
        log.tracebuf.push(TraceEntry::LinkSup2(li, lkind, ri0, ritem0.kind(), ri, ritem.kind()).into());
      }
      _ => {
        unimplemented!();
      }
    }
    if self.trace {
    println!("DEBUG:  _link_sup2: li={:?} ri0={:?} ritem0={:?} ri={:?} ritem={:?}", li, ri0, ritem0, ri, ritem);
    }
    if !self.items.insert(ri0, ritem0).is_none() {
      return e_bot();
    }
    if !self.tree_.jux.insert(ri, ri0).is_none() {
      return e_bot();
    }
    // FIXME: enforce convex tree condition.
    match self.items.get_mut(&ri0) {
      // TODO TODO
      Some(&mut Item_::Ctl_(.., ref mut arg)) => {
        *arg = Some(ri);
      }
      Some(ritem0) => {
        if self.trace {
        println!("DEBUG:  _link_sup2:  ritem0={:?}", ritem0);
        }
        unimplemented!();
      }
      None => {
        if self.trace {
        println!("DEBUG:  _link_sup2:  no ritem0");
        }
        panic!("bug");
      }
    }
    if !self.items.insert(ri, ritem).is_none() {
      return e_bot();
    }
    if !self.tree_.sup.insert(ri0, li).is_none() {
      return e_bot();
    }
    match self.items.get_mut(&li) {
      // TODO TODO
      Some(&mut Item_::Name_(.., ref mut vargs)) |
      Some(&mut Item_::Head_(.., ref mut vargs)) |
      Some(&mut Item_::PHead_(.., ref mut vargs)) |
      Some(&mut Item_::Pred_(.., ref mut vargs)) |
      Some(&mut Item_::Unify_(.., ref mut vargs)) => {
        vargs.push(ri0);
      }
      Some(litem) => {
        println!("DEBUG:  _link_sup2:  litem={:?}", litem);
        unimplemented!();
      }
      None => {
        println!("DEBUG:  _link_sup2:  no litem");
        panic!("bug");
      }
    }
    self._recompile(ri)
  }

  pub fn _link_sup_(&mut self, li: ItemNum, ri: ItemNum, ritem: Item_) -> Result<(), Err_> {
    let lkind = match self.items.get(&li) {
      None => panic!("bug"),
      Some(litem) => litem.kind()
    };
    match &mut self.mode {
      &mut DrawMode::Replay{ref mut log} => {
        log.tracebuf.push(TraceEntry::LinkSup_(li, lkind, ri, ritem.kind()).into());
      }
      _ => {
        unimplemented!();
      }
    }
    if self.trace {
    println!("DEBUG:  _link_sup_:  li={:?} ri={:?} ritem={:?}", li, ri, ritem);
    }
    if !self.items.insert(ri, ritem).is_none() {
      return e_bot();
    }
    if !self.tree_.sup.insert(ri, li).is_none() {
      return e_bot();
    }
    // FIXME: enforce convex tree condition.
    match self.items.get_mut(&li) {
      // TODO TODO
      Some(&mut Item_::Name_(.., ref mut vargs)) |
      Some(&mut Item_::Head_(.., ref mut vargs)) |
      Some(&mut Item_::PHead_(.., ref mut vargs)) |
      Some(&mut Item_::Pred_(.., ref mut vargs)) |
      Some(&mut Item_::Unify_(.., ref mut vargs)) |
      Some(&mut Item_::Arg0_(.., ref mut vargs)) => {
        vargs.push(ri);
      }
      Some(litem) => {
        println!("DEBUG:  _link_sup_:  litem={:?}", litem);
        unimplemented!();
      }
      None => {
        println!("DEBUG:  _link_sup_:  no litem");
        panic!("bug");
      }
    }
    self._recompile(ri)
  }

  pub fn _anchor(&mut self, i: ItemNum, item: Item_) -> Result<(), Err_> {
    match &mut self.mode {
      &mut DrawMode::Replay{ref mut log} => {
        log.tracebuf.push(TraceEntry::Anchor(i, item.kind()).into());
      }
      _ => {
        unimplemented!();
      }
    }
    if self.tree_.root.is_some() {
      return e_bot();
    }
    if self.trace {
    println!("DEBUG:  _anchor:     i={:?} item={:?}", i, item);
    }
    assert!(self.items.insert(i, item).is_none());
    self.tree_.root = Some(i);
    self._recompile(i)
  }

  pub fn _pop(&self) -> Option<ItemNum> {
    if self.query.borrow().pop_done {
      return None;
    }
    loop {
      let i = match match self.query.borrow().pop_ub {
        None => {
          self.items.range(..).rev().next()
        }
        Some(ub) => {
          self.items.range( .. ub).rev().next()
        }
      } {
        None => None,
        Some((&i, item)) => {
          match item {
            &Item_::Stop_(_) => None,
            _ => Some(i)
          }
        }
      };
      match i {
        None => {
          self.query.borrow_mut().pop_done = true;
          return None;
        }
        Some(i) => {
          self.query.borrow_mut().pop_ub = Some(i);
          if self.query.borrow().iter_set.contains(&i) {
            continue;
          }
          self.query.borrow_mut().iter_set.insert(i);
          return Some(i);
        }
      }
    }
  }

  pub fn _left(&self, i: ItemNum) -> Option<ItemNum> {
    match self.tree_.jux.get(&i) {
      None => None,
      Some(&j) => {
        self.query.borrow_mut().iter_set.insert(j);
        Some(j)
      }
    }
  }

  pub fn _up(&self, i: ItemNum) -> Option<ItemNum> {
    match self.tree_.sup.get(&i) {
      None => None,
      Some(&j) => {
        self.query.borrow_mut().iter_set.insert(j);
        Some(j)
      }
    }
  }

  pub fn _reduce_item2(&mut self, pre_cursor: (ItemNum, Item_), cursor: (ItemNum, Item_)) -> Result<(), Err_> {
    // FIXME FIXME
    let (prekey, pre_cursor) = pre_cursor;
    let (curkey, cursor) = cursor;
    match &mut self.mode {
      &mut DrawMode::Replay{ref mut log} => {
        //log.ctlp += 1;
        log.tracebuf.push(TraceEntry::ReduceItem2(prekey, pre_cursor.kind(), curkey, cursor.kind()).into());
      }
      _ => {
        unimplemented!();
      }
    }
    if self.trace {
    println!("DEBUG:  _reduce_item2: pre={:?} cur={:?}", pre_cursor, cursor);
    }
    self.query.borrow_mut()._reset();
    match &cursor {
      &Item_::Stop_(_) => {
        return e_bot();
      }
      _ => {}
    }
    loop {
      match &pre_cursor {
        &Item_::Ctl_(ref ctl_s, ..) => {
          let ctl_kind = CtlKind::from(ctl_s.as_raw_str());
          let mat_arg = match &cursor {
            &Item_::Name_(..) => ItemKind::name_(),
            &Item_::Head_(..) => ItemKind::head_(),
            &Item_::PHead_(..) => ItemKind::phead_(),
            &Item_::Unify_(..) => ItemKind::unify_(),
            &Item_::Pred_(..) => ItemKind::pred_(),
            _ => ItemKind::empty()
          };
          let mat_like = match &cursor {
            &Item_::Name_(..) => ItemKind::name_() | ItemKind::head_() | ItemKind::phead_(),
            &Item_::Head_(..) => ItemKind::head_() | ItemKind::name_() | ItemKind::phead_(),
            &Item_::PHead_(..) => ItemKind::head_() | ItemKind::name_() | ItemKind::phead_(),
            &Item_::Unify_(..) => ItemKind::unify_() | ItemKind::pred_(),
            &Item_::Pred_(..) => ItemKind::pred_() | ItemKind::unify_(),
            _ => ItemKind::empty()
          };
          let mat_all =
              ItemKind::name_()
            | ItemKind::head_()
            | ItemKind::phead_()
            | ItemKind::unify_()
            | ItemKind::pred_()
          ;
          let mat_rest = mat_like - mat_arg;
          match ctl_kind {
            CtlKind::Comma |
            CtlKind::CommaAnd |
            CtlKind::And => {
              // TODO TODO
              let popkey = match self._pop() {
                None => break,
                Some(p) => p
              };
              let mut accept = Vec::new();
              let mut root = popkey;
              let (nobrk, mat, acc) = match self.draw_uni(3)? {
                0 => (mat_like, mat_all, mat_arg),
                1 => (mat_like, mat_all, mat_rest),
                2 => (mat_all, mat_all, mat_all - mat_like),
                _ => unimplemented!()
              };
              let rootk = self._get_item(root)?.kind();
              /*if (rootk & mat).is_none() {
                return e_bot();
              }*/
              if (rootk & nobrk).is_none() {
                return e_bot();
              }
              if (rootk & acc).is_some() {
                accept.push(root);
              }
              loop {
                let mut p = root;
                if self.trace {
                println!("DEBUG:  _reduce_item2:     p={:?} (left)", p);
                println!("DEBUG:  _reduce_item2:       tree.sup ={:?}", &self.tree_.sup);
                println!("DEBUG:  _reduce_item2:       tree.jux ={:?}", &self.tree_.jux);
                }
                loop {
                  match self._left(p) {
                    Some(q) => {
                      if self.trace {
                      println!("DEBUG:  _reduce_item_:     left: {:?} <-- {:?}", q, p);
                      }
                      p = q;
                      continue;
                    }
                    None => break
                  }
                }
                if self.trace {
                println!("DEBUG:  _reduce_item2:     p={:?} (up)", p);
                println!("DEBUG:  _reduce_item2:       tree.sup ={:?}", &self.tree_.sup);
                println!("DEBUG:  _reduce_item2:       tree.jux ={:?}", &self.tree_.jux);
                }
                match self._up(p) {
                  Some(q) => {
                    if self.trace {
                    println!("DEBUG:  _reduce_item_:     up:   {:?} <-- {:?}", q, p);
                    }
                    let qk = self._get_item(q)?.kind();
                    root = q;
                    if (qk & nobrk).is_none() {
                      break;
                    }
                    if (qk & mat).is_some() {
                      if (qk & acc).is_some() {
                        accept.push(root);
                      }
                      continue;
                    /*} else {
                      break;*/
                    }
                  }
                  None => break
                }
              }
              if self.trace {
              println!("DEBUG:  _reduce_item2:   accept={:?}", accept);
              }
              for &cand in accept.iter().rev() {
                match self.draw_uni(min(accept.len() as UDraw, 2))? {
                  0 => {
                    if self.trace {
                    println!("DEBUG:  _reduce_item2: cand={:?} pre={:?} {:?} cur={:?} {:?}", cand, prekey, pre_cursor, curkey, cursor);
                    }
                    self._link_sup2(cand, prekey, pre_cursor, curkey, cursor)?;
                    return Ok(());
                  }
                  1 => {}
                  _ => unimplemented!()
                }
              }
            }
            CtlKind::Of |
            CtlKind::With => {
              let popkey = match self._pop() {
                None => break,
                Some(p) => p
              };
              match self._get_item(popkey)? {
                &Item_::Head_(..) => {
                  self._link_sup2(popkey, prekey, pre_cursor, curkey, cursor)?;
                  return Ok(());
                }
                _ => {}
              }
            }
            CtlKind::At |
            CtlKind::In |
            CtlKind::On => {
              let popkey = match self._pop() {
                None => break,
                Some(p) => p
              };
              let mut accept = Vec::new();
              let mut root = popkey;
              let mat = mat_all | ItemKind::ctl_();
              let acc = ItemKind::pred_();
              let rootk = self._get_item(root)?.kind();
              if (rootk & mat).is_none() {
                //println!("DEBUG:  _reduce_item2: accept={:?} root={:?} rootk={:?} mat={:?}", accept, root, rootk, mat);
                return e_bot();
              }
              if (rootk & acc).is_some() {
                accept.push(root);
              }
              loop {
                let mut p = root;
                loop {
                  match self._left(p) {
                    Some(q) => {
                      p = q;
                      continue;
                    }
                    None => break
                  }
                }
                match self._up(p) {
                  Some(q) => {
                    let qk = self._get_item(q)?.kind();
                    root = q;
                    if (qk & mat).is_some() {
                      if (qk & acc).is_some() {
                        accept.push(root);
                      }
                      continue;
                    } else {
                      break;
                    }
                  }
                  None => break
                }
              }
              for &cand in accept.iter().rev() {
                match self.draw_uni(2)? {
                  0 => {
                    if self.trace {
                    println!("DEBUG:  _reduce_item2: cand={:?} pre={:?} {:?} cur={:?} {:?}", cand, prekey, pre_cursor, curkey, cursor);
                    }
                    self._link_sup2(cand, prekey, pre_cursor, curkey, cursor)?;
                    return Ok(());
                  }
                  1 => {}
                  _ => unimplemented!()
                }
              }
            }
            _ => {
            }
          }
        }
        _ => {}
      }
      break;
    }
    e_top()
  }

  pub fn _reduce_item_(&mut self, cursor: (ItemNum, Item_)) -> Result<(), Err_> {
    let (curkey, cursor) = cursor;
    match &mut self.mode {
      &mut DrawMode::Replay{ref mut log} => {
        //log.ctlp += 1;
        log.tracebuf.push(TraceEntry::ReduceItem_(curkey, cursor.kind()).into());
      }
      _ => {
        unimplemented!();
      }
    }
    if self.trace {
    println!("DEBUG:  _reduce_item_: cur={:?}", cursor);
    }
    self.query.borrow_mut()._reset();
    match &cursor {
      &Item_::Stop_(_) => {
        if self.tree_.root.is_none() {
          return e_bot();
        }
        if !self.items.insert(curkey, cursor).is_none() {
          return e_bot();
        }
        self._recheck_root()?;
        let root = self.tree_.root.take().unwrap();
        self.tree_.rootstop.push((root, curkey));
        match &mut self.mode {
          &mut DrawMode::Replay{ref mut log} => {
            log.tracebuf.push(TraceEntry::RootStop_(root, curkey).into());
          }
          _ => {}
        }
        return Ok(());
      }
      _ => {}
    }
    if self.tree_.root.is_none() {
      return self._anchor(curkey, cursor);
    }
    loop {
      match &cursor {
        &Item_::Stop_(_) => {
          return e_bot();
        }
        &Item_::Name_(..) => {
          let popkey = match self._pop() {
            None => break,
            Some(p) => p
          };
          match self._get_item(popkey)? {
            &Item_::Ctl_(..) => {
              // TODO TODO
            }
            &Item_::Head_(..) => {
              // TODO TODO
              self._link_sup_(popkey, curkey, cursor)?;
              return Ok(());
            }
            &Item_::Pred_(..) => {
              self._link_sup_(popkey, curkey, cursor)?;
              return Ok(());
            }
            &Item_::Unify_(..) => {
              self._link_sup_(popkey, curkey, cursor)?;
              return Ok(());
            }
            &Item_::Arg0_(..) => {
              self._link_sup_(popkey, curkey, cursor)?;
              return Ok(());
            }
            _ => {
            }
          }
        }
        &Item_::Head_(..) => {
          let popkey = match self._pop() {
            None => break,
            Some(p) => p
          };
          match self._get_item(popkey)? {
            &Item_::Ctl_(..) => {
              // TODO TODO
            }
            &Item_::PHead_(..) => {
              if self.trace {
              println!("DEBUG:  _reduce_item_: curkey={:?} cursor={:?} popkey={:?} PHead", curkey, cursor, popkey);
              }
              self._link_sup_(popkey, curkey, cursor)?;
              return Ok(());
            }
            &Item_::Pred_(..) => {
              self._link_sup_(popkey, curkey, cursor)?;
              return Ok(());
            }
            &Item_::Unify_(..) => {
              //println!("DEBUG:  _reduce_item_: curkey={:?} cursor={:?} popkey={:?}", curkey, cursor, popkey);
              self._link_sup_(popkey, curkey, cursor)?;
              return Ok(());
            }
            &Item_::Arg0_(..) => {
              self._link_sup_(popkey, curkey, cursor)?;
              return Ok(());
            }
            _ => {
            }
          }
        }
        &Item_::PHead_(..) => {
          let popkey = match self._pop() {
            None => break,
            Some(p) => p
          };
          match self._get_item(popkey)? {
            &Item_::Ctl_(..) => {
              // TODO TODO
            }
            &Item_::PHead_(..) => {
              self._link_sup_(popkey, curkey, cursor)?;
              return Ok(());
            }
            &Item_::Pred_(..) => {
              self._link_sup_(popkey, curkey, cursor)?;
              return Ok(());
            }
            &Item_::Unify_(..) => {
              if self.trace {
              println!("DEBUG:  _reduce_item_: curkey={:?} cursor={:?} popkey={:?} Unify", curkey, cursor, popkey);
              }
              self._link_sup_(popkey, curkey, cursor)?;
              return Ok(());
            }
            &Item_::Arg0_(..) => {
              self._link_sup_(popkey, curkey, cursor)?;
              return Ok(());
            }
            _ => {
            }
          }
        }
        &Item_::Unify_(..) => {
          // TODO TODO
          let popkey = match self._pop() {
            None => break,
            Some(p) => p
          };
          match self._get_item(popkey)? {
            &Item_::Name_(..) |
            &Item_::Head_(..) |
            &Item_::PHead_(..) => {
              let mut accept = Vec::new();
              let mut root = popkey;
              accept.push(root);
              loop {
                let mut p = root;
                loop {
                  match self._left(p) {
                    Some(q) => {
                      p = q;
                      continue;
                    }
                    None => break
                  }
                }
                match self._up(p) {
                  Some(q) => {
                    let qk = self._get_item(q)?.kind();
                    root = q;
                    if (qk & ItemKind::unify_()).is_some() ||
                       (qk & ItemKind::pred_()).is_some() ||
                       (qk & ItemKind::arg0_()).is_some()
                    {
                      break;
                    }
                    if (qk & ItemKind::name_()).is_some() ||
                       (qk & ItemKind::head_()).is_some() ||
                       (qk & ItemKind::phead_()).is_some()
                    {
                      accept.push(root);
                      continue;
                    }
                  }
                  None => break
                }
              }
              //println!("DEBUG:  _reduce_item_: curkey={:?} cursor={:?} popkey={:?} accept={:?}", curkey, cursor, popkey, accept);
              for &cand in accept.iter().rev() {
                // TODO TODO
                match self.draw_uni(min(accept.len() as UDraw, 2))? {
                  0 => {
                    self._link_sup_(cand, curkey, cursor)?;
                    return Ok(());
                  }
                  1 => {}
                  _ => unimplemented!()
                }
              }
            }
            _ => {}
          }
        }
        &Item_::Pred_(ref _pred_s, ..) => {
          // TODO TODO
          let popkey = match self._pop() {
            None => break,
            Some(p) => p
          };
          if self.trace {
          println!("DEBUG:  _reduce_item_:   popkey={:?}", popkey);
          }
          let brk =
              ItemKind::unify_()
            | ItemKind::pred_()
          ;
          let mat =
              ItemKind::name_()
            | ItemKind::head_()
            | ItemKind::phead_()
          ;
          let acc = mat;
          let mut accept = Vec::new();
          let mut root = popkey;
          let rootk = self._get_item(root)?.kind();
          if (rootk & brk).is_some() {
            return e_bot();
          }
          if (rootk & acc).is_some() {
            accept.push(root);
          }
          if self.trace {
          println!("DEBUG:  _reduce_item_:   root={:?}", root);
          }
          loop {
            let mut p = root;
            if self.trace {
            println!("DEBUG:  _reduce_item_:     p={:?} (left)", p);
            println!("DEBUG:  _reduce_item_:       tree.sup ={:?}", &self.tree_.sup);
            println!("DEBUG:  _reduce_item_:       tree.jux ={:?}", &self.tree_.jux);
            }
            loop {
              match self._left(p) {
                Some(q) => {
                  if self.trace {
                  println!("DEBUG:  _reduce_item_:     left: {:?} <-- {:?}", q, p);
                  }
                  p = q;
                  continue;
                }
                None => break
              }
            }
            if self.trace {
            println!("DEBUG:  _reduce_item_:     p={:?} (up)", p);
            println!("DEBUG:  _reduce_item_:       tree.sup ={:?}", &self.tree_.sup);
            println!("DEBUG:  _reduce_item_:       tree.jux ={:?}", &self.tree_.jux);
            }
            match self._up(p) {
              Some(q) => {
                if self.trace {
                println!("DEBUG:  _reduce_item_:     up:   {:?} <-- {:?}", q, p);
                }
                let qk = self._get_item(q)?.kind();
                root = q;
                if (qk & brk).is_some() {
                  break;
                }
                if (qk & mat).is_some() {
                  if (qk & acc).is_some() {
                    accept.push(root);
                  }
                  continue;
                }
              }
              None => break
            }
          }
          if self.trace {
          println!("DEBUG:  _reduce_item_:   accept={:?}", accept);
          }
          for &cand in accept.iter().rev() {
            match self.draw_uni(min(accept.len() as UDraw, 2))? {
              0 => {
                if self.trace {
                println!("DEBUG:  _reduce_item_: cand={:?} cur={:?} {:?}", cand, curkey, cursor);
                }
                self._link_sup_(cand, curkey, cursor)?;
                return Ok(());
              }
              1 => {}
              _ => unimplemented!()
            }
          }
        }
        &Item_::Ctl_(ref ctl_s, ..) => {
          let ctl_kind = CtlKind::from(ctl_s.as_raw_str());
          let mat_all =
              ItemKind::name_()
            | ItemKind::head_()
            | ItemKind::phead_()
            | ItemKind::unify_()
            | ItemKind::pred_()
          ;
          match ctl_kind {
            CtlKind::Again => {
              let popkey = match self._pop() {
                None => break,
                Some(p) => p
              };
              let mut accept = Vec::new();
              let mut root = popkey;
              let mat = mat_all;
              let acc = ItemKind::pred_();
              let rootk = self._get_item(root)?.kind();
              if (rootk & mat).is_none() {
                return e_bot();
              }
              if (rootk & acc).is_some() {
                accept.push(root);
              }
              loop {
                let mut p = root;
                loop {
                  match self._left(p) {
                    Some(q) => {
                      p = q;
                      continue;
                    }
                    None => break
                  }
                }
                match self._up(p) {
                  Some(q) => {
                    let qk = self._get_item(q)?.kind();
                    root = q;
                    if (qk & mat).is_none() {
                      break;
                    }
                    if (qk & acc).is_some() {
                      accept.push(root);
                    }
                  }
                  None => break
                }
              }
              for &cand in accept.iter().rev() {
                match self.draw_uni(2)? {
                  0 => {
                    if self.trace {
                    println!("DEBUG:  _reduce_item_: cand={:?} cur={:?} {:?}", cand, curkey, cursor);
                    }
                    self._link_sup_(cand, curkey, cursor)?;
                    return Ok(());
                  }
                  1 => {}
                  _ => unimplemented!()
                }
              }
            }
            _ => {
            }
          }
        }
        _ => {
        }
      }
      break;
    }
    e_top()
  }

  pub fn _redraw(&mut self) -> Result<(), Err_> {
    self.math = false;
    self.itemctr = 0;
    self.prevstage.clear();
    self.stage.clear();
    self.items.clear();
    self.nodes.clear();
    self.tree_._reset();
    'outer: loop {
      if self._cur_items_len() <= 0 {
        match self.draw_uni(2)? {
          0 => {
            // FIXME: explicit test for halt.
            break 'outer;
          }
          1 => {}
          _ => unimplemented!()
        }
      }
      match self.draw_uni(3)? {
        0 => {
          match self.draw_uni(5)? {
            4 => {
              self.exact_decode_trie([" "])?;
              let (name_s, name) = self.decode_latex_name_()?;
              self._push_item_(Item_::name_(name_s, name))?;
            }
            3 => {
              match self.draw_uni(2)? {
                0 => {
                  self.auto_decode_trie([" the", " an", " a"])?;
                }
                1 => {}
                _ => unimplemented!()
              }
              let s = self.auto_decode_trie([
                  " point",
                  " triangle",
                  " $\\angle",
                  " angle bisector",
                  " angle",
                  " line segment",
                  " line",
                  " segment",
                  " circle",
                  " quadrilateral",
                  " parallelogram",
                  " trapezoid",
                  " polygon",
                  " pentagon",
                  " hexagon",
                  " side",
                  " circumcircle",
                  " incircle",
                  " midpoint",
                  " diagonal",
                  " diameter",
                  " circumcenter",
                  " circumcentre",
                  " circumradius",
                  " incenter",
                  " incentre",
                  " orthocenter",
                  " orthocentre",
                  " feet",
                  " foot",
                  " altitude",
                  " perpendicular bisector",
                  " external angle bisector",
                  " external bisector",
                  " exterior angle bisector",
                  " exterior bisector",
              ])?;
              let start = s.start + 1;
              let end = s.end;
              let val = s.val.get(1 .. ).unwrap().into();
              let s = AttrStr{start, end, val};
              // FIXME: math mode.
              if &s.val == "feet" {
                self._push_item_(Item_::mult_head_(s, None))?;
              } else {
                match self.draw_uni(2)? {
                  0 => {
                    // FIXME FIXME: do this _before_ items push.
                    let qs = self.exact_decode_trie(["s"])?;
                    // TODO TODO: item?
                    self._push_item_(Item_::mult_head_(s, qs))?;
                  }
                  1 => {
                    self._push_item_(Item_::head_(s))?;
                  }
                  _ => unimplemented!()
                }
              }
            }
            2 => {
              let _a = match self.draw_uni(2)? {
                0 => {
                  self.auto_decode_trie([" the", " an", " a"])?;
                  true
                }
                1 => false,
                _ => unimplemented!()
              };
              let s = self.auto_decode_trie([
                  // TODO TODO
                  // FIXME: negation.
                  " not",
                  // FIXME: "its", "it" etc.
                  " its",
                  // FIXME: numbers Mult.
                  " two",
                  " convex",
                  " parallel",
                  " cyclic",
                  " distinct",
                  " similar",
                  " equilateral",
                  " acute-angled",
                  " acute",
                  " isosceles",
                  " right-angled",
                  " right",
                  " obtuse-angled",
                  " obtuse",
                  " scalene",
                  " concurrent",
                  " collinear",
                  " concyclic",
                  " equal",
              ])?;
              let start = s.start + 1;
              let end = s.end;
              let val = s.val.get(1 .. ).unwrap().into();
              let s = AttrStr{start, end, val};
              // FIXME FIXME
              /*self._push_item(Item_::Desc(s))?;*/
              //if !a {
              self._push_item_(Item_::PHead_(s, Vec::new()))?;
              //}
            }
            1 => {
              let s = self.auto_decode_trie([
                  " lies", " lie",
                  " meets", " meet",
                  " intersects", " intersect",
                  " bisects", " bisect",
                  " passes",
              ])?;
              let start = s.start + 1;
              let end = s.end;
              let val = s.val.get(1 .. ).unwrap().into();
              let s = AttrStr{start, end, val};
              // TODO TODO
              self._push_item_(Item_::pred_(s))?;
            }
            0 => {
              // FIXME FIXME: for "and" and comma,
              // Join case in addition to Mult case.
              // TODO TODO: also put Sep case here?
              let s = self.auto_decode_trie([
                  // TODO TODO
                  ", and", ",", " and",
                  " be", " are", " is",
                  " form",
                  " has", " have",
                  " of",
                  " with", " whose",
                  " at",
                  " in",
                  " on",
                  " through",
                  " from",
                  " again",
              ])?;
              match s.as_raw_str() {
                "," | ", and" | " and" => {
                  match self.draw_uni(1)? {
                    0 => {
                      match s.as_raw_str() {
                        ", and" => {
                          // FIXME: a little context dependence.
                          let mut comma = false;
                          for &(ctl, _) in self.prevstage.iter().rev() {
                            match self.items.get(&ctl) {
                              Some(&Item_::Ctl_(ref ctl_s, ..)) => {
                                let ctl_kind = CtlKind::from(ctl_s.as_raw_str());
                                match ctl_kind {
                                  CtlKind::Comma => {
                                    comma = true;
                                    break;
                                  }
                                  _ => {}
                                }
                              }
                              _ => {}
                            }
                          }
                          if comma {
                            match self.draw_uni(2)? {
                              1 => {
                                self._push_item_(Item_::Stop_(s))?;
                              }
                              0 => {
                                self._stage_item(Item_::Ctl_(s, None))?;
                              }
                              _ => unimplemented!()
                            }
                          } else {
                            match self.draw_uni(2)? {
                              0 => {
                                self._push_item_(Item_::Stop_(s))?;
                              }
                              1 => {
                                self._stage_item(Item_::Ctl_(s, None))?;
                              }
                              _ => unimplemented!()
                            }
                          }
                        }
                        "," => {
                          self._stage_item(Item_::Ctl_(s, None))?;
                        }
                        " and" => {
                          let start = s.start + 1;
                          let end = s.end;
                          let val = s.val.get(1 .. ).unwrap().into();
                          let s = AttrStr{start, end, val};
                          self._stage_item(Item_::Ctl_(s, None))?;
                        }
                        _ => unimplemented!()
                      }
                    }
                    _ => unimplemented!()
                  }
                }
                _ => {
                  let start = s.start + 1;
                  let end = s.end;
                  let val = s.val.get(1 .. ).unwrap().into();
                  let s = AttrStr{start, end, val};
                  // FIXME FIXME
                  // FIXME: upper case.
                  // FIXME: "form" should probably not be Unify_.
                  if &s.val == "be" || &s.val == "are" || &s.val == "is" || &s.val == "form" {
                    // TODO TODO
                    self._push_item_(Item_::unify_(s))?;
                  } else if &s.val == "has" || &s.val == "have" {
                    // TODO TODO
                  } else if &s.val == "of" {
                    self._stage_item(Item_::Ctl_(s, None))?;
                  } else if &s.val == "with" || &s.val == "whose" {
                    self._stage_item(Item_::Ctl_(s, None))?;
                  } else if &s.val == "at" {
                    self._stage_item(Item_::Ctl_(s, None))?;
                  } else if &s.val == "in" {
                    self._stage_item(Item_::Ctl_(s, None))?;
                  } else if &s.val == "on" {
                    self._stage_item(Item_::Ctl_(s, None))?;
                  } else if &s.val == "through" {
                    self._stage_item(Item_::Ctl_(s, None))?;
                  } else if &s.val == "from" {
                    self._stage_item(Item_::Ctl_(s, None))?;
                  } else if &s.val == "again" {
                    self._push_item_(Item_::Ctl_(s, None))?;
                  }
                }
              }
            }
            _ => unimplemented!()
          }
        }
        1 => {
          // FIXME: should Arg0_ these.
          let s = self.auto_decode_trie([
              " let", " suppose", " denote",
              " assume", " in", " given",
              " consider", " define",
              //" then",
              " such that",
              // TODO TODO
              //"if", "then",
              " prove",
              //" show",
              //" determine",
          ])?;
          match s.as_raw_str() {
            " Suppose" |
            " suppose" => {
              match self.draw_uni(2)? {
                0 => {
                  self.auto_decode_trie([" also"])?;
                }
                1 => {}
                _ => unimplemented!()
              }
              match self.draw_uni(2)? {
                0 => {
                  self.auto_decode_trie([" that"])?;
                }
                1 => {}
                _ => unimplemented!()
              }
              match self.draw_uni(2)? {
                0 => {
                  self.auto_decode_trie([" there"])?;
                  let s = self.auto_decode_trie([
                      // FIXME
                      " has", " have",
                      " exists", " is",
                      " exist", " are",
                  ])?;
                  match s.as_raw_str() {
                    // FIXME
                    " Has" | " Have" |
                    " has" | " have" => {
                    }
                    " Exists" | " Is" |
                    " exists" | " is" => {
                    }
                    " Exist" | " Are" |
                    " exist" | " are" => {
                    }
                    _ => unimplemented!()
                  }
                }
                1 => {}
                _ => unimplemented!()
              }
            }
            " Denote" |
            " denote" => {
              match self.draw_uni(2)? {
                0 => {
                  self.auto_decode_trie([" by"])?;
                }
                1 => {}
                _ => unimplemented!()
              }
            }
            " Assume" |
            " assume" => {
              match self.draw_uni(2)? {
                0 => {
                  self.auto_decode_trie([" that"])?;
                }
                1 => {}
                _ => unimplemented!()
              }
            }
            " Prove" |
            " prove" => {
              match self.draw_uni(2)? {
                0 => {
                  self.auto_decode_trie([" that"])?;
                }
                1 => {}
                _ => unimplemented!()
              }
            }
            _ => {}
          }
          match s.as_raw_str() {
            " Prove" |
            " prove" => {
              let start = s.start + 1;
              let end = s.end;
              let val = s.val.get(1 .. ).unwrap().into();
              let s = AttrStr{start, end, val};
              self._push_item_(Item_::Arg0_(s, Vec::new()))?;
            }
            // FIXME FIXME: hack.
            " such that" => {
              let start = s.start + 1;
              let end = s.end;
              let val = s.val.get(1 .. ).unwrap().into();
              let s = AttrStr{start, end, val};
              self._push_item_(Item_::Stop_(s))?;
            }
            _ => {
              // FIXME FIXME: hack until Arg0.
              if self.tree_.root.is_some() {
                return e_bot();
              }
              /*self._push_item_(Item_::Arg0(_))?;*/
            }
          }
        }
        2 => {
          match self.draw_uni(2)? {
            0 => {
              self.auto_decode_trie([
                  ", too", " too",
                  ", respectively", " respectively",
                  " analogously",
              ])?;
            }
            1 => {}
            _ => unimplemented!()
          }
          match self.draw_uni(2)? {
            0 => {
              let s = match self.eof_decode() {
                Err(_) => {
                  self.exact_decode_trie([".", ";", "?", "!"])?
                }
                Ok(s) => s
              };
              self._push_item_(Item_::Stop_(s))?;
            }
            1 => {
              let s = self.auto_decode_trie([",", " and"])?;
              match s.as_raw_str() {
                " and" => {
                  let start = s.start + 1;
                  let end = s.end;
                  let val = s.val.get(1 .. ).unwrap().into();
                  let s = AttrStr{start, end, val};
                  self._push_item_(Item_::Stop_(s))?;
                }
                _ => {
                  self._push_item_(Item_::Stop_(s))?;
                }
              }
            }
            _ => unimplemented!()
          }
          continue 'outer;
        }
        _ => unimplemented!()
      }
    } // loop 'outer
    Ok(())
  }
}
