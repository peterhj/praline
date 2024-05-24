extern crate praline;
extern crate rustc_serialize;
extern crate time;

use praline::algo::*;
use praline::geometry::*;
use rustc_serialize::json::{JsonLines, encode_to_string};
use time::*;

use std::cmp::{Ordering, max};
use std::fs::{File, OpenOptions};
use std::io::{Write};

#[derive(Debug, RustcDecodable)]
pub struct Item {
  pub key: SmolStr,
  pub slice: i32,
  pub val: SmolStr,
}

#[derive(Debug, RustcEncodable)]
pub struct OutItem {
  pub i: usize,
  pub result: SmolStr,
  pub match_: Option<SmolStr>,
  pub val: SmolStr,
}

#[derive(Debug, RustcEncodable)]
pub struct ErrItem {
  pub i: usize,
  pub result: SmolStr,
  pub rem: f64,
  pub inc_val: SmolStr,
  pub val: SmolStr,
}

fn main() {
  let mut items = Vec::new();
  let jit = JsonLines::from_reader(File::open("data/geom_r135.jsonl").unwrap());
  for j in jit {
    let j = j.unwrap();
    let item = j.decode_into::<Item>().unwrap();
    items.push((item.key, item.val));
  }
  let mut out_f = OpenOptions::new().create(true).write(true).truncate(true).open("tmp.out").unwrap();
  let mut err_f = OpenOptions::new().create(true).write(true).truncate(true).open("tmp.err").unwrap();
  let mut geom = Geometry::default();
  let mut ok_list = Vec::new();
  let mut ok_bt_list = Vec::new();
  let mut ok_ct = 0;
  let mut err_ct = 0;
  let mut ok_bt_sum = 0;
  let mut bt_sum = 0;
  let mut ok_bt_max = 0;
  let mut bt_max = 0;
  let mut ok_dt_sum = 0.0;
  let mut dt_sum = 0.0;
  let mut unmatch: Vec<(_, _, SmolStr)> = Vec::new();
  println!("INFO:   n={}", items.len());
  let mut key_comp: BTreeMap<_, [i32; 2]> = BTreeMap::new();
  let adhoc_start = items.len();
  for (i, (key, val)) in items.iter().enumerate() {
    geom.reset_replay();
    //geom.set_backtrace_limit(1000);
    geom.set_backtrace_limit(3000);
    //geom.set_backtrace_limit(10_000);
    if false && i >= adhoc_start {
      geom.set_trace(true);
    } else {
      geom.set_trace(false);
    }
    let t0 = get_time();
    let res = geom.match_(val);
    match res {
      Ok(_) => {
        let t1 = get_time();
        let dt = (t1 - t0).to_std().unwrap();
        let dt = dt.as_secs() as f64 + 1.0e-9 * dt.subsec_nanos() as f64;
        let btct = geom._backtrace_count();
        ok_list.push(i);
        ok_bt_list.push(btct);
        ok_ct += 1;
        ok_bt_sum += btct;
        ok_bt_max = max(ok_bt_max, btct);
        ok_dt_sum += dt;
        dt_sum += dt;
        match key_comp.get_mut(key) {
          None => {
            key_comp.insert(key.clone(), [1, 1]);
          }
          Some(&mut [ref mut nv, ref mut dv]) => {
            *nv += 1;
            *dv += 1;
          }
        }
        println!("INFO:   i={} ok dt={:.09}", i, dt);
      }
      Err(_) => {
        let t1 = get_time();
        let dt = (t1 - t0).to_std().unwrap();
        let dt = dt.as_secs() as f64 + 1.0e-9 * dt.subsec_nanos() as f64;
        err_ct += 1;
        dt_sum += dt;
        match key_comp.get_mut(key) {
          None => {
            key_comp.insert(key.clone(), [0, 1]);
          }
          Some(&mut [_, ref mut dv]) => {
            *dv += 1;
          }
        }
        println!("INFO:   i={} err dt={:.09}", i, dt);
        unmatch.push((TotalOrd(1.0 - geom.emit_longest_str().len() as f64 / val.len() as f64), i, geom.emit_longest_str().into()));
      }
    }
    // NB: uncomment for extra debug output.
    /*
    for (i, name) in geom._names().iter().enumerate() {
      println!("DEBUG:  name[{}]={:?}", i, name);
    }
    for (i, item) in geom._items().enumerate() {
      println!("DEBUG:  item[{:?}]={:?}", item.0, item.1);
    }
    for (i, node) in geom._nodes() {
      println!("DEBUG:  node[{:?}]={:?}", i, node);
    }
    for i in geom._roots() {
      println!("DEBUG:  root[{:?}]={:?}", i, geom._node_lookup(i));
    }
    */
    if let Ok(_) = res {
      if let Ok(s) = geom._render_praline() {
        println!("INFO:   P={:?}", s);
        let item = OutItem{
          i: i,
          result: "ok".into(),
          match_: Some(s.into()),
          val: val.into(),
        };
        writeln!(&mut out_f, "{}", encode_to_string(&item).unwrap()).unwrap();
      } else {
        println!("INFO:   P=bot");
        let item = OutItem{
          i: i,
          result: "ok".into(),
          match_: None,
          val: val.into(),
        };
        writeln!(&mut out_f, "{}", encode_to_string(&item).unwrap()).unwrap();
      }
    }
    println!("INFO:   S=\"{}\"", geom.emit_longest_str());
    println!("INFO:   s=\"{}\"", geom.emit_str());
    println!("INFO:   v=\"{}\"", val);
    println!("INFO:   k=\"{}\"", key);
    println!("INFO:   btct={}", geom._backtrace_count());
    bt_sum += geom._backtrace_count();
    bt_max = max(bt_max, geom._backtrace_count());
  }
  let mut key_comp_sorted = Vec::new();
  for (key, &[nv, dv]) in key_comp.iter() {
    key_comp_sorted.push((TotalOrd(1.0 - nv as f64 / dv as f64), key.clone()));
  }
  key_comp_sorted.sort();
  for &(_, ref key) in key_comp_sorted.iter().take(20) {
    let &[nv, dv] = key_comp.get(key).unwrap();
    println!("INFO:   key=\"{}\" nv={} dv={}", key, nv, dv);
  }
  unmatch.sort();
  let mut err_zlen_ct = 0;
  for &(rem, i, ref s) in unmatch.iter() {
    let &(_, ref val) = &items[i];
    if s == " " || s.len() <= 0 {
      err_zlen_ct += 1;
    }
    let item = ErrItem{
      i: i,
      result: "err".into(),
      rem: rem.0,
      inc_val: s.into(),
      val: val.into(),
    };
    writeln!(&mut err_f, "{}", encode_to_string(&item).unwrap()).unwrap();
  }
  println!("INFO:   oklist={:?}", ok_list);
  println!("INFO:   okbtct={:?}", ok_bt_list);
  println!("INFO:   ok  ct={}", ok_ct);
  println!("INFO:   err ct={}", err_ct);
  println!("INFO:   err zl={}", err_zlen_ct);
  println!("INFO:   ok  bt sum={}", ok_bt_sum);
  println!("INFO:   ok  bt max={}", ok_bt_max);
  println!("INFO:   ok  dt sum={:.09}", ok_dt_sum);
  println!("INFO:   bt sum={}", bt_sum);
  println!("INFO:   bt max={}", bt_max);
  println!("INFO:   dt sum={:.09}", dt_sum);
}

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct TotalOrd<F: Copy>(pub F);

impl PartialEq for TotalOrd<f64> {
  fn eq(&self, other: &TotalOrd<f64>) -> bool {
    match self.cmp(other) {
      Ordering::Equal => true,
      _ => false
    }
  }
}

impl Eq for TotalOrd<f64> {}

impl PartialOrd for TotalOrd<f64> {
  fn partial_cmp(&self, other: &TotalOrd<f64>) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for TotalOrd<f64> {
  fn cmp(&self, other: &TotalOrd<f64>) -> Ordering {
    self.to_signed_ord_bits().cmp(&other.to_signed_ord_bits())
  }
}

impl TotalOrd<f64> {
  #[inline]
  pub fn to_ord_bits(&self) -> u64 {
    // NB: This should be the same 1-to-1 mapping as done by `total_cmp`
    // in libcore.
    let mut bits = (self.0).to_bits();
    bits ^= ((((bits as i64) >> 63) as u64) >> 1);
    bits
  }

  #[inline]
  pub fn to_signed_ord_bits(&self) -> i64 {
    self.to_ord_bits() as i64
  }
}
