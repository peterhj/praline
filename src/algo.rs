pub use crate::re::{len_utf8};

pub use fxhash::{FxHashMap, FxHashSet};
pub use smol_str::{SmolStr};

pub use std::collections::{HashMap, HashSet};
pub use std::collections::{BTreeMap, BTreeSet};
use std::convert::{TryInto};
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

pub trait Optional {
  fn is_none(&self) -> bool;

  #[inline]
  fn is_some(&self) -> bool {
    !self.is_none()
  }
}

impl<T> Optional for Vec<T> {
  #[inline]
  fn is_none(&self) -> bool {
    self.is_empty()
  }
}

pub fn safe_ascii(s: &[u8]) -> SmolStr {
  let mut buf = String::new();
  for &x in s.iter() {
    if x <= 0x20 {
      buf.push(' ');
    } else if x < 0x7f {
      buf.push(x.try_into().unwrap());
    } else {
      buf.push('?');
    }
  }
  buf.into()
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SafeStr {
  raw:  SmolStr,
}

impl From<SmolStr> for SafeStr {
  fn from(raw: SmolStr) -> SafeStr {
    SafeStr{raw}
  }
}

impl From<String> for SafeStr {
  fn from(s: String) -> SafeStr {
    SafeStr{raw: s.into()}
  }
}

impl<'a> From<&'a str> for SafeStr {
  fn from(s: &'a str) -> SafeStr {
    SafeStr{raw: s.into()}
  }
}

impl SafeStr {
  pub fn is_empty(&self) -> bool {
    self.raw.is_empty()
  }

  pub fn as_raw_str(&self) -> &str {
    self.raw.as_str()
  }

  pub fn set_raw_str<S: Into<SmolStr>>(&mut self, s: S) {
    self.raw = s.into();
  }
}

impl Debug for SafeStr {
  fn fmt(&self, f: &mut Formatter) -> FmtResult {
    write!(f, "{:?}", safe_ascii(self.raw.as_bytes()))
  }
}

impl Display for SafeStr {
  fn fmt(&self, f: &mut Formatter) -> FmtResult {
    write!(f, "{}", safe_ascii(self.raw.as_bytes()))
  }
}

// NB: json-like string (un-)escape via rustc_serialize.

fn decode_hex_escape<I: Iterator<Item=char>>(src: &mut I) -> Result<u16, ()> {
  let mut i = 0;
  let mut n = 0;
  while i < 4 {
    let c = match src.next() {
      Some(c) => c,
      None => return Err(())
    };
    n = match c {
      c @ '0' ..= '9' => n * 16 + ((c as u16) - ('0' as u16)),
      c @ 'a' ..= 'f' => n * 16 + (10 + (c as u16) - ('a' as u16)),
      c @ 'A' ..= 'F' => n * 16 + (10 + (c as u16) - ('A' as u16)),
      _ => return Err(())
    };
    i += 1;
  }
  Ok(n)
}

pub fn unescape_chars<I: Iterator<Item=char>>(src: &mut I, delim: char) -> Result<String, ()> {
  let c = match src.next() {
    None => {
      return Err(());
    }
    Some(c) => c
  };
  if c != delim {
    return Err(());
  }

  let mut res = String::new();
  let mut escape = false;

  loop {
    let c = match src.next() {
      None => {
        return Err(());
      }
      Some(c) => c
    };

    if escape {
      match c {
        '"' => res.push('"'),
        '\\' => res.push('\\'),
        // NB: must escape single-char latex delimiter.
        '$' => res.push('$'),
        '/' => res.push('/'),
        'b' => res.push('\x08'),
        'f' => res.push('\x0c'),
        'n' => res.push('\n'),
        'r' => res.push('\r'),
        't' => res.push('\t'),
        'u' => match decode_hex_escape(src)? {
          0xDC00 ..= 0xDFFF => {
            //return self.error(LoneLeadingSurrogateInHexEscape)
            return Err(());
          }

          // Non-BMP characters are encoded as a sequence of
          // two hex escapes, representing UTF-16 surrogates.
          n1 @ 0xD800 ..= 0xDBFF => {
            match (src.next(), src.next()) {
              (Some('\\'), Some('u')) => (),
              //_ => return self.error(UnexpectedEndOfHexEscape),
              _ => return Err(())
            }

            let n2 = decode_hex_escape(src)?;
            if n2 < 0xDC00 || n2 > 0xDFFF {
              //return self.error(LoneLeadingSurrogateInHexEscape)
              return Err(());
            }
            let c = (((n1 - 0xD800) as u32) << 10 |
                 (n2 - 0xDC00) as u32) + 0x1_0000;
            res.push(char::from_u32(c).unwrap());
          }

          n => match char::from_u32(n as u32) {
            Some(c) => res.push(c),
            //None => return self.error(InvalidUnicodeCodePoint),
            None => return Err(())
          },
        },
        //_ => return self.error(InvalidEscape),
        _ => return Err(())
      }
      escape = false;
    } else if c == '\\' {
      escape = true;
    } else {
      if c == delim {
        return Ok(res);
      } else if c <= '\u{1F}' {
        //return self.error(ControlCharacterInString),
        return Err(());
      } else {
        res.push(c);
      }
    }
  }
}

pub fn escape_str(src: &str, delim: char) -> String {
  let mut dst = String::new();
  dst.push(delim);

  let mut start = 0;

  for (i, byte) in src.bytes().enumerate() {
    let escaped = match byte {
      b'"' => "\\\"",
      b'\\' => "\\\\",
      // NB: must escape single-char latex delimiter.
      b'$' => "\\$",
      b'\x00' => "\\u0000",
      b'\x01' => "\\u0001",
      b'\x02' => "\\u0002",
      b'\x03' => "\\u0003",
      b'\x04' => "\\u0004",
      b'\x05' => "\\u0005",
      b'\x06' => "\\u0006",
      b'\x07' => "\\u0007",
      b'\x08' => "\\b",
      b'\t' => "\\t",
      b'\n' => "\\n",
      b'\x0b' => "\\u000b",
      b'\x0c' => "\\f",
      b'\r' => "\\r",
      b'\x0e' => "\\u000e",
      b'\x0f' => "\\u000f",
      b'\x10' => "\\u0010",
      b'\x11' => "\\u0011",
      b'\x12' => "\\u0012",
      b'\x13' => "\\u0013",
      b'\x14' => "\\u0014",
      b'\x15' => "\\u0015",
      b'\x16' => "\\u0016",
      b'\x17' => "\\u0017",
      b'\x18' => "\\u0018",
      b'\x19' => "\\u0019",
      b'\x1a' => "\\u001a",
      b'\x1b' => "\\u001b",
      b'\x1c' => "\\u001c",
      b'\x1d' => "\\u001d",
      b'\x1e' => "\\u001e",
      b'\x1f' => "\\u001f",
      b'\x7f' => "\\u007f",
      _ => { continue; }
    };

    if start < i {
      dst.push_str(&src[start..i]);
    }

    dst.push_str(escaped);

    start = i + 1;
  }

  if start != src.len() {
    dst.push_str(&src[start..]);
  }

  dst.push(delim);
  dst
}

pub fn normalize_str(src: &str) -> (String, Vec<u32>) {
  let mut dst = String::new();
  let mut org = Vec::new();
  let mut off = 0;
  let mut space = false;
  if let Some(c) = src.chars().next() {
    if !c.is_whitespace() {
      dst.push(' ');
      org.push(off);
      space = true;
    }
  }
  for c in src.chars() {
    let c_len = len_utf8(c as _) as u32;
    if c.is_whitespace() {
      if !space {
        dst.push(' ');
        org.push(off);
        space = true;
      }
    } else {
      dst.push(c);
      for _ in 0 .. c_len {
        org.push(off);
      }
      space = false;
    }
    off += c_len;
  }
  if space {
    dst.truncate(dst.len() - 1);
    org.pop();
  }
  org.push(off);
  (dst, org)
}
