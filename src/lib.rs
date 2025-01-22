//! # `ccl_rs`
//! This is a parser for the **Categorical Configuration Language**.
//!
//! The structure of the language is that every parsed [CCL document](Model) is a (possibly empty)
//! map from [String]s to [CCL document](Model)s.
//!
//! ``` ignore
//! CCL = Mapping[String -> CCL]
//! ```
//!
//! This crate makes the following change from the language as described
//! [here](https://chshersh.com/blog/2025-01-06-the-most-elegant-configuration-language.html):
//!
//! We assume that a string without a `=` sign parses as a key with empty value. That is,
//! ``` ignore
//! parse_kv("some string") == KeyValue{key = "some string", value="" };
//! ```
//! Interesingly this then means that _no UTF-8 string is invalid as a CCL document_, and so
//! the [`load`] function is error free. There is no other change to the language apart from
//! the fact that strings without `=` are now valid:
//!
//! ```rust
//! # use ccl_rs::load;
//! let model = load("this is just a key".to_owned());
//! assert_eq!(model.as_singleton(), Some("this is just a key"));
//! ```
//!
//! ## Examples
//!
//! To parse a CCL document
//!
//! ```rust
//! # use ccl_rs::load;
//! let model = load("
//! /= This is a CCL document
//! language = rust
//! library = ccl_rs
//! author =
//!   name = Robert Spencer
//!   species = human
//! ".to_owned());
//! ```
//!
//! Scalars in `CCL` don't exist, and the nearest we have are "singletons": maps from strings to
//! the empty map. We can try cast a model to a singleton with [`Model::as_singleton`].
//!
//! ```rust
//! # use ccl_rs::load;
//! let singleton = load("
//! a singleton =
//! ".to_owned());
//! assert_eq!(singleton.as_singleton(), Some("a singleton"));
//! ```
//!
//! We can destructure the document with [`Model::get`]
//!
//! ```rust
//! # use ccl_rs::load;
//! # fn main() -> std::result::Result<(), ccl_rs::CCLError> {
//! # let model = load("
//! # /= This is a CCL document
//! # language = rust
//! # library = ccl_rs
//! # author =
//! #   name = Robert Spencer
//! #   species = human
//! # ".to_owned());
//! assert_eq!(model.get("author")?.get("species")?.as_singleton(), Some("human"));
//! assert_eq!(model.at(["author", "species"])?.as_singleton(), Some("human"));
//! # Ok(())
//! # }
//! ```
//! However, [`Model::as_singleton`] should rarely actually be used. You should prefer
//! [`Model::value`] which casts the singleton value (as a string) to its generic parameter using
//! [`FromStr`].
//! ```rust
//! # use ccl_rs::load;
//! # fn main() -> std::result::Result<(), ccl_rs::CCLError> {
//! let model = load("
//! listen =
//!   host = 127.0.0.1
//!   port = 80
//! daemon = true
//! ".to_owned());
//! // We can use the turbo fish to force the type ...
//! assert_eq!(model.at(["listen", "port"])?.value::<u16>()?, 80u16);
//! // ... or leave it inferred.
//! let host : std::net::Ipv4Addr = model.at(["listen", "host"])?.value()?;
//! //         ^^^^^^^^^^^^^^^^^^ Here we've type hinted, but this might be inferred in other ways
//! // Even bools are parsed
//! if !model.get("daemon")?.value()? {
//!   panic!()
//! }
//! # Ok(())
//! # }
//! ```
//! There are two suggested methods for denoting lists and `ccl_rs` provides [`Model::as_list`] that
//! handles both. Either a list can be valuless keys:
//! ```rust
//! # use ccl_rs::load;
//! # fn main() -> std::result::Result<(), ccl_rs::CCLError> {
//! let model = load("
//! fruits =
//!  apples =
//!  pears =
//!  tomatoes =
//! ".to_owned());
//! assert_eq!(
//!   model.get("fruits")?.as_list().map(|x| x.value().unwrap()).collect::<Vec<String>>(),
//!   ["apples", "pears", "tomatoes"]
//! );
//! # Ok(())
//! # }
//! ```
//! Or it can be keyless values
//! ```rust
//! # use ccl_rs::load;
//! # fn main() -> std::result::Result<(), ccl_rs::CCLError> {
//! let model = load("
//! fruits =
//!  = apples
//!  = pears
//!  = tomatoes
//! ".to_owned());
//! assert_eq!(
//!   model.get("fruits")?.as_list().map(|x| x.value().unwrap()).collect::<Vec<String>>(),
//!   ["apples", "pears", "tomatoes"]
//! );
//! # Ok(())
//! # }
//! ```
//!
//! ## Fold
//! Let us suppose you have two configurations: one from the user and one from the system
//! settings.
//! ```rust
//! # use ccl_rs::{Model, load};
//! # fn main() -> std::result::Result<(), ccl_rs::CCLError> {
//! let system = load("
//! font size = 12px
//! colour scheme = gruvbox
//! ".to_owned());
//! let user = load("
//! colour scheme = dracula
//! ".to_owned());
//! # Ok(())
//! # }
//! ```
//! This gives the model:
//! The `CCL` method of combining these is either [`Model::merge`], or the equivalent of concatting
//! the strings and then parsing. This gives:
//! ```rust
//! # use ccl_rs::{Model, load};
//! # fn main() -> std::result::Result<(), ccl_rs::CCLError> {
//! # let system = load("
//! # font size = 12px
//! # colour scheme = gruvbox
//! # ".to_owned());
//! # let user = load("
//! # colour scheme = dracula
//! # ".to_owned());
//! let configuration = Model::merge(system, user);
//! # Ok(())
//! # }
//! ```
//! This gives
//! ``` ignore
//! colour scheme =
//!   dracula =
//!   gruvbox =
//! font size = 12px
//! ```
//! However, we could do
//! ```rust
//! # use ccl_rs::{Model, load};
//! # fn main() -> std::result::Result<(), ccl_rs::CCLError> {
//! # let system = load("
//! # font size = 12px
//! # colour scheme = gruvbox
//! # ".to_owned());
//! # let user = load("
//! # colour scheme = dracula
//! # ".to_owned());
//! let configuration = Model::merge(
//!   Model::intro("system".to_string(), system),
//!   Model::intro("user".to_string(), user),
//! );
//! # Ok(())
//! # }
//! ```
//! which is
//! ``` ignore
//! system =
//!   font size = 12px
//!   colour scheme = gruvbox
//! user =
//!   colour scheme = dracula
//! ```
//! Now if the application wants to know which colour scheme to use, it could query `["user",
//! "colour scheme"]` and `["system", "colour scheme"]` and apply precidence. But if we have the
//! rule that user configuration always trumps system configuration, we can apply the [`Model::fold`]
//! operator instead as follows:
//! ```rust
//! # use ccl_rs::{Model, load};
//! # fn main() -> std::result::Result<(), ccl_rs::CCLError> {
//! # let system = load("
//! # font size = 12px
//! # colour scheme = gruvbox
//! # ".to_owned());
//! # let user = load("
//! # colour scheme = dracula
//! # ".to_owned());
//! let configuration = Model::merge(
//!   Model::intro("system".to_string(), system),
//!   Model::intro("user".to_string(), user),
//! ).fold();
//! # Ok(())
//! # }
//! ```
//! which gives
//! ``` ignore
//! font size =
//!   12px = system
//! colour scheme =
//!   gruvbox = system
//!   dracula = user
//! ```
//! and then the application code can simply do
//! ```rust
//! # use ccl_rs::{Model, load};
//! # fn main() -> std::result::Result<(), ccl_rs::CCLError> {
//! # let system = load("
//! # font size = 12px
//! # colour scheme = gruvbox
//! # ".to_owned());
//! # let user = load("
//! # colour scheme = dracula
//! # ".to_owned());
//! # let configuration = Model::merge(
//! #   Model::intro("system".to_string(), system),
//! #   Model::intro("user".to_string(), user),
//! # ).fold();
//! let colour_scheme: String = configuration
//!     .get("colour scheme")?
//!     .as_list()
//!     .last()
//!     .unwrap()
//!     .value()?;
//! assert_eq!(colour_scheme, "dracula");
//! # Ok(())
//! # }
//! ```
mod maps;

use std::str::FromStr;

use itertools::Itertools;
use maps::{Map, StringMapLike};

#[derive(Debug)]
struct ValueEntry(Map<Vec<ValueEntry>>);

#[derive(Debug, PartialEq, Eq)]
struct KeyValue {
    key: String,
    value: String,
}

type KVList = Vec<KeyValue>;
fn indent(s: &str) -> usize {
    s.len() - s.trim_start_matches(' ').len()
}
fn parse(s: String) -> KVList {
    let mut ans = KVList::new();
    let s = s.strip_prefix("\n").unwrap_or(&s);
    let first_indent = indent(s);
    let s = s.trim_start();
    if s.is_empty() {
        ans
    } else if let Some((first_key, rest)) = s.split_once('=') {
        let mut lines = rest
            .trim_start_matches(' ')
            .trim_end()
            .split("\n")
            .enumerate();
        let first_value: String = lines
            .take_while_ref(|(i, x)| *i == 0 || indent(x) > first_indent || x.is_empty())
            .map(|(_, x)| x)
            .join("\n")
            .trim_end()
            .to_owned();
        let remainder = lines.map(|(_, x)| x).join("\n");
        ans.push(KeyValue {
            key: first_key.trim().to_owned(),
            value: first_value.to_owned(),
        });
        ans.append(&mut parse(remainder));
        ans
    } else {
        ans.push(KeyValue {
            key: s.trim().to_owned(),
            value: String::new(),
        });
        ans
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum CCLError {
    MissingKey,
    ValueOfMapping,
    ParseError,
}

/// ## Construction
/// [`Model`]s should be constructed using [`Model::empty`], [`Model::singleton`] and
/// [`Model::intro`] along with [`Model::merge`]. Alternatively they can be parsed from strings
/// using [`load`].
#[derive(Hash, Clone, Debug, PartialEq, Eq, Default)]
pub struct Model(Map<Model>);
impl Model {
    /// Create an empty model
    pub fn empty() -> Model {
        Model(Map::new())
    }
    /// Construct a singleton model
    ///
    /// A "singleton" is a map from a single key to the empty model.
    pub fn singleton(value: String) -> Model {
        Model::intro(value, Model::empty())
    }
    /// Create a single key-value pair
    pub fn intro(key: String, value: Model) -> Model {
        Model(Map::from([(key, value)]))
    }
    /// Combine two models
    ///
    /// This is the monoid action on the monoid of models. It is associative and has unit
    /// [`Model::empty()`]. It works by concatenation and then combination of keys. The
    /// order of keys is preserved so that the keys of `Model::merge(a, b)` are exactly those of
    /// `a` followed by those of `b` that are not in `a`. If a key appears in both `a` and `b`, the
    /// contents are combined again using `Model::merge`.
    pub fn merge(a: Model, b: Model) -> Model {
        Self::union(a, b, Model::merge)
    }
    pub fn fold(self) -> Model {
        if self.len() == 1 {
            if self.is_singleton() {
                return self;
            }
            let key = self.keys().next().unwrap().to_owned();
            let value = self.values().next().unwrap();
            value
                .split()
                .map(|m| {
                    Model(
                        m.into_iter()
                            .map(|(k, v)| (k, Model([(key.clone(), v)].into()).fold()))
                            .collect(),
                    )
                })
                .fold(Model::empty(), Model::merge)
        } else {
            self.split()
                .map(Self::fold)
                .fold(Model::empty(), Model::merge)
        }
    }
    fn split(&self) -> impl Iterator<Item = Model> + use<'_> {
        self.iter()
            .map(|(k, v)| Model([(k.to_owned(), v.clone())].into()))
    }
    /// Extracts the singleton value of this [`Model`].
    ///
    /// See [`Model::singleton`] for the constructor.
    pub fn as_singleton(&self) -> Option<&str> {
        if self.len() == 1 && self.values().all_equal_value() == Ok(&Self::empty()) {
            self.keys().next()
        } else {
            None
        }
    }
    fn is_singleton(&self) -> bool {
        self.as_singleton().is_some()
    }
    pub fn as_list(&self) -> impl Iterator<Item = Model> + use<'_> {
        if self.len() == 1 {
            if let Ok(children) = self.get("") {
                return children.as_list();
            }
        }
        self.split()
    }
    fn fmt_indented(&self, f: &mut std::fmt::Formatter<'_>, indent: usize) -> std::fmt::Result {
        if let Some(key) = self.as_singleton() {
            write!(f, "{key}")?;
            return Ok(());
        }
        if self.keys().all_equal_value() == Ok("") {
            let lst = self.get("").unwrap();
            if lst.split().all(|x| x.is_singleton()) {
                for (i, v) in lst.keys().enumerate() {
                    if i > 0 {
                        writeln!(f)?;
                    }
                    write!(f, "{0:indent$}{}= {v}", "")?;
                }
                return Ok(());
            }
        }
        for (i, (k, v)) in self.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }
            write!(
                f,
                "{0:indent$}{k} ={1}",
                "",
                if v.is_singleton() {
                    " "
                } else if v == &Model::empty() {
                    ""
                } else {
                    "\n"
                }
            )?;
            v.fmt_indented(f, indent + 2)?;
        }
        Ok(())
    }
    pub fn get(&self, key: &str) -> Result<&Model, CCLError> {
        <Self as StringMapLike<_>>::get(self, key).ok_or(CCLError::MissingKey)
    }
    pub fn at<'a>(&self, keys: impl IntoIterator<Item = &'a str>) -> Result<&Model, CCLError> {
        keys.into_iter().try_fold(self, Self::get)
    }
    pub fn value<T: FromStr>(&self) -> Result<T, CCLError> {
        if let [key] = self.keys().collect::<Vec<_>>().as_slice() {
            key.parse().map_err(|_| CCLError::ParseError)
        } else {
            Err(CCLError::ValueOfMapping)
        }
    }
}
impl std::fmt::Display for Model {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_indented(f, 0)
    }
}
impl IntoIterator for Model {
    type Item = (String, Model);

    type IntoIter = ordermap::map::IntoIter<String, Model>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}
impl StringMapLike<Model> for Model {
    fn keys(&self) -> impl Iterator<Item = &str> {
        StringMapLike::keys(&self.0)
    }

    fn values<'a>(&'a self) -> impl Iterator<Item = &'a Model>
    where
        Model: 'a,
    {
        StringMapLike::values(&self.0)
    }

    fn get(&self, key: &str) -> Option<&Model> {
        StringMapLike::get(&self.0, key)
    }

    fn insert(&mut self, key: String, value: Model) {
        StringMapLike::insert(&mut self.0, key, value);
    }

    fn len(&self) -> usize {
        StringMapLike::len(&self.0)
    }

    fn iter<'a>(&'a self) -> impl Iterator<Item = (&'a str, &'a Model)>
    where
        Model: 'a,
    {
        StringMapLike::iter(&self.0)
    }
}

fn fix_entry_map(mp: Map<Vec<ValueEntry>>) -> Model {
    Model(
        mp.into_iter()
            .map(|(k, v)| {
                (
                    k,
                    v.into_iter()
                        .map(|em| fix_entry_map(em.0))
                        .fold(Model::empty(), Model::merge),
                )
            })
            .collect(),
    )
}
fn add_key_val(
    mut mp: Map<Vec<ValueEntry>>,
    KeyValue { key, value }: KeyValue,
) -> Map<Vec<ValueEntry>> {
    let value: ValueEntry = ValueEntry(of_key_vals(parse(value.clone())));
    mp.entry(key).or_default().push(value);
    mp
}
fn of_key_vals(kvlist: KVList) -> Map<Vec<ValueEntry>> {
    kvlist.into_iter().fold(Map::new(), add_key_val)
}
fn fix(kvlist: KVList) -> Model {
    fix_entry_map(of_key_vals(kvlist))
}
/// Parse a string into a CCL model
pub fn load(s: String) -> Model {
    fix(parse(s))
}

#[cfg(test)]
mod test {
    use super::*;
    use rstest::rstest;

    macro_rules! kv {
        [$k:expr => $v: expr] => {
            KeyValue { key: $k.to_owned(), value: $v.to_owned() }
        };
    }

    const STRESS_DOCUMENT: &str = "
/= This is a CCL document
title = CCL Example

database =
  enabled = true
  ports =
    = 8000
    = 8001
    = 8002
  limits =
    cpu = 1500mi
    memory = 10Gb

user =
  guestId = 42

user =
  login = chshersh
  createdAt = 2024-12-31

multiline = 
  this value wraps
  over the line!
";
    macro_rules! stress_model {
        () => {
            model![
                "/" => model![ "This is a CCL document" ],
                "title" => model![ "CCL Example" ],
                "database" => model![
                    "enabled" => model![ "true" ],
                    "ports" => model![
                        "" => model! ["8000", "8001", "8002"]
                    ],
                    "limits" => model![
                        "cpu" => model![ "1500mi" ],
                        "memory" => model![ "10Gb" ],
                    ]
                ],
                "user" => model![
                    "guestId" => model![ "42" ] ,
                    "login" => model![ "chshersh" ],
                    "createdAt" => model![ "2024-12-31" ]
                ],
                "multiline" => model![
                    "this value wraps\n  over the line!"
                ]
            ]
        }
    }

    macro_rules! kvl {
            [$($k:expr => $v:expr),* $(,)?] => {
                vec![$(kv![$k => $v]),*]
            };
        }
    macro_rules! model_term {
        ($k:literal => $v:expr) => {
            ($k.to_owned(), $v)
        };
        ($k:literal) => {
            ($k.to_owned(), Model::empty())
        };
    }
    macro_rules! model {
            [$($k:literal $(=> $v:expr)?),* $(,)?] => {
                Model ( Map::from([
                     $(model_term!($k $( => $v)?)),*
                ]) )
            };
        }
    mod test_parser {
        use super::*;
        // We use a macro to panic in the function
        macro_rules! assert_parse_iter {
            ($input:expr, $expected:expr) => {
                assert_eq!(
                    parse($input.to_owned()).iter().collect::<Vec<_>>(),
                    $expected
                )
            };
        }

        mod test_empty {
            use super::*;

            #[rstest]
            fn test_empty(
                #[values("", " ", "   ", "\n", "  \n", "\n\n", "  \n  \n  ")] input: &str,
            ) {
                assert!(parse(input.to_owned()).is_empty())
            }
        }
        mod test_multiple {
            use super::*;
            use pretty_assertions::assert_eq;
            #[test]
            fn test_two() {
                assert_parse_iter!(
                    "key1 = val1\nkey2 = val2",
                    [&kv!["key1" => "val1"], &kv!["key2" => "val2"]]
                )
            }
            #[test]
            fn test_untrimmed() {
                assert_parse_iter!(
                    "
key1 = val1
key2 = val2
",
                    [&kv!["key1" => "val1"], &kv!["key2" => "val2"]]
                )
            }
            #[test]
            fn test_real() {
                assert_parse_iter!(
                    "
name = Dmitrii Kovanikov
login = chshersh
language = OCaml
date = 2024-05-25
",
                    [
                        &kv!["name" => "Dmitrii Kovanikov"],
                        &kv!["login" => "chshersh"],
                        &kv!["language" => "OCaml"],
                        &kv!["date" => "2024-05-25"],
                    ]
                )
            }
            #[test]
            fn test_list_like() {
                assert_parse_iter!(
                    "
= 3
= 1
= 2
",
                    [&kv!["" => "3"], &kv!["" => "1"], &kv!["" => "2"]]
                )
            }
            #[test]
            fn test_array_like() {
                assert_parse_iter!(
                    "
1 =
2 =
3 =
",
                    [&kv!["1" => ""], &kv!["2" => ""], &kv!["3" => ""]]
                )
            }
        }
        mod test_nested {
            use super::*;
            use pretty_assertions::assert_eq;
            #[test]
            fn test_single_line() {
                assert_parse_iter!(
                    "
key =
  val
",
                    [&kv!["key" => "\n  val"]]
                )
            }
            #[test]
            fn test_multi_line() {
                assert_parse_iter!(
                    "
key =
  line1
  line2
",
                    [&kv!["key" => "\n  line1\n  line2"]]
                )
            }
            #[test]
            fn test_multi_line_skip() {
                assert_parse_iter!(
                    "
key =
  line1

  line2
",
                    [&kv!["key" => "\n  line1\n\n  line2"]]
                )
            }
            #[test]
            fn test_nested_key_value() {
                assert_parse_iter!(
                    "
key =
  field1 = value1
  field2 = value2
",
                    [&kv!["key" => "\n  field1 = value1\n  field2 = value2"]]
                )
            }
            #[test]
            fn test_nested_deep_key_value() {
                assert_parse_iter!(
                    "
key =
  field1 = value1
  field2 =
    subfield = x
    another = y
",
                    [&kv![
                        "key" =>
                        "\n  field1 = value1\n  field2 =\n    subfield = x\n    another = y"
                    ]]
                )
            }
        }
        mod test_single {
            use super::*;
            use pretty_assertions::assert_eq;
            #[rstest]
            fn test_no_value(#[values("key", "  key", "key  ", "  key  ")] input: &str) {
                assert_parse_iter!(input, [&kv!["key" => ""]])
            }
            #[rstest]
            fn test_single(
                #[values(
                    "key=val",
                    "key = val",
                    "  key = val",
                    "key = val  ",
                    " key  =  val  ",
                    "\nkey = val\n",
                    "key \n= val\n",
                    "  \n key  \n=  val  \n"
                )]
                input: &str,
            ) {
                assert_parse_iter!(input, [&kv!["key" => "val"]])
            }
            #[rstest]
            fn test_empty_value(#[values("key =", "key =\n", "key =  ", "key =  \n")] input: &str) {
                assert_parse_iter!(input, [&kv!["key" => ""]])
            }
            #[rstest]
            fn test_empty_key(#[values("= val", "  = val", "\n  = val")] input: &str) {
                assert_parse_iter!(input, [&kv!["" => "val"]])
            }
            #[rstest]
            fn test_empty_key_value(#[values("=", "  =  ", "\n  =  \n")] input: &str) {
                assert_parse_iter!(input, [&kv!["" => ""]])
            }
            #[test]
            fn test_multiple_equality() {
                assert_parse_iter!("a=b=c", [&kv!["a" => "b=c"]])
            }
            #[test]
            fn test_multiple_equality2() {
                assert_parse_iter!("a = b = c", [&kv!["a" => "b = c"]])
            }
            #[test]
            fn test_empty_equality() {
                assert_parse_iter!(" = = ", [&kv!["" => "="]])
            }
            #[test]
            fn test_section() {
                assert_parse_iter!("== Section 2 ==", [&kv!["" => "= Section 2 =="]])
            }
            #[test]
            fn test_comment() {
                assert_parse_iter!("/= this is a comment", [&kv!["/" => "this is a comment"]])
            }
        }
        mod test_stress {
            use super::*;
            use pretty_assertions::assert_eq;
            #[test]
            fn test_stress() {
                assert_parse_iter!(
                    STRESS_DOCUMENT,
                    [
                        &kv!["/" => "This is a CCL document"],
                        &kv!["title" => "CCL Example"],
                        &kv![
                            "database" =>
                            "
  enabled = true
  ports =
    = 8000
    = 8001
    = 8002
  limits =
    cpu = 1500mi
    memory = 10Gb"
                        ],
                        &kv!["user" => "\n  guestId = 42"],
                        &kv!["user" => "\n  login = chshersh\n  createdAt = 2024-12-31"],
                        &kv!["multiline" => "\n  this value wraps\n  over the line!"],
                    ]
                )
            }
        }
        mod test_value {
            use super::*;
            use pretty_assertions::assert_eq;
            #[test]
            fn test_empty() {
                assert!(parse("".to_owned()).is_empty())
            }
            #[ignore]
            #[test]
            fn test_spaces() {
                assert!(parse("   ".to_owned()).is_empty(),)
            }
            #[test]
            fn test_eol() {
                assert!(parse("\n".to_owned()).is_empty())
            }
            #[test]
            fn test_just_string() {
                assert_parse_iter!("val", [&kv!["val" => ""]])
            }
            #[test]
            fn test_empty_key_val() {
                assert_parse_iter!("=", [&kv!["" => ""]])
            }
            #[test]
            fn test_multi_line_plain() {
                assert_parse_iter!("val\n  next", [&kv!["val\n  next" => ""]])
            }
            #[test]
            fn test_multi_line_plain_nested() {
                assert_parse_iter!(
                    "val
  next",
                    [&kv!["val
  next" => ""]]
                )
            }
            #[test]
            fn test_kv_single() {
                assert_parse_iter!(
                    "
key = val",
                    [&kv!["key" => "val"]]
                )
            }
            #[test]
            fn test_kv_multiple() {
                assert_parse_iter!(
                    "
key1 = val1
key2 = val2",
                    [&kv!["key1" => "val1"], &kv!["key2" => "val2"]]
                )
            }
            #[test]
            fn test_kv_multiple_indented() {
                assert_parse_iter!(
                    "
    key1 = val1
    key2 = val2",
                    [&kv!["key1" => "val1"], &kv!["key2" => "val2"]]
                )
            }
            #[test]
            fn test_kv_multiple_nested() {
                assert_parse_iter!(
                    "
key1 = val1
  inner = some
key2 = val2",
                    [
                        &kv!["key1" => "val1\n  inner = some"],
                        &kv!["key2" => "val2"]
                    ]
                )
            }
        }
    }
    mod test_fix {
        use super::*;
        use pretty_assertions::assert_eq;
        #[test]
        fn test_empty() {
            assert_eq!(fix(kvl![]), Model::empty())
        }
        #[test]
        fn test_single() {
            assert_eq!(
                fix(kvl!["key" => "value"]),
                model!["key" => model!["value" => Model::empty()]]
            )
        }
        #[test]
        fn test_double() {
            assert_eq!(
                fix(kvl!["key1" => "value1", "key2" => "value2"]),
                model![
                    "key1" => model!["value1" => Model::empty()],
                    "key2" => model!["value2" => Model::empty()],
                ]
            )
        }
        #[test]
        fn test_stress() {
            assert_eq!(
                fix(kvl![
                     "/" => "This is a CCL document",
                     "title" => "CCL Example",
                     "database" => "
  enabled = true
  ports =
    = 8000
    = 8001
    = 8002
  limits =
    cpu = 1500mi
    memory = 10Gb",
                     "user" => "\n  guestId = 42",
                     "user" => "\n  login = chshersh\n  createdAt = 2024-12-31",
                     "multiline" => "\n  this value wraps\n  over the line!",
                ]),
                stress_model!()
            );
        }
    }
    mod test_pretty {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        fn test_empty() {
            assert_eq!(format!("{}", model![]), "")
        }
        #[test]
        fn test_single_key_val() {
            assert_eq!(format!("{}", model!["key" => model![ "val" ]]), "key = val")
        }
        #[test]
        fn test_two_keys_vals() {
            assert_eq!(
                format!(
                    "{}",
                    model!["key1" => model![ "val1" ], "key2" => model![ "val2" ]]
                ),
                "key1 = val1\nkey2 = val2"
            )
        }
        #[test]
        fn test_singleton() {
            assert_eq!(format!("{}", model!["key"]), "key")
        }
        #[test]
        fn test_list() {
            assert_eq!(
                format!("{}", model!["" => model! [ "key1", "key2" ]]),
                "= key1\n= key2"
            )
        }
        #[test]
        fn test_other_list() {
            assert_eq!(format!("{}", model!["key1", "key2"]), "key1 =\nkey2 =")
        }
        #[test]
        fn test_map_of_singletons() {
            assert_eq!(
                format!("{}", model!["key" => model! [ "value1", "value2" ]]),
                "key =\n  value1 =\n  value2 ="
            )
        }
        #[test]
        fn test_stress() {
            assert_eq!(
                format!("{}", stress_model!()),
                "/ = This is a CCL document
title = CCL Example
database =
  enabled = true
  ports =
    = 8000
    = 8001
    = 8002
  limits =
    cpu = 1500mi
    memory = 10Gb
user =
  guestId = 42
  login = chshersh
  createdAt = 2024-12-31
multiline = this value wraps
  over the line!"
            )
        }
    }
    mod test_property {
        use super::*;
        use rand::distributions::{Alphanumeric, Uniform};
        use rand::{Rng, SeedableRng};
        use rand_chacha::ChaCha8Rng;

        fn random_ccl(rng: &mut impl Rng, width: usize, depth: usize) -> Model {
            let this_width = if rng.sample(Uniform::new(0, depth)) == 0 {
                0
            } else {
                rng.sample(Uniform::new(width / 2, width + 1))
            };
            Model(
                std::iter::repeat_with(|| {
                    (
                        std::iter::repeat_with(|| rng.sample(Alphanumeric) as char)
                            .take(3)
                            .collect(),
                        random_ccl(rng, width, depth - 1),
                    )
                })
                .take(this_width)
                .collect(),
            )
        }

        #[rstest]
        fn test_roundtrip(
            #[values(1, 2, 3)] seed: u64,
            #[values(4, 5, 6)] width: usize,
            #[values(1, 4, 8)] depth: usize,
        ) {
            let mut rng = ChaCha8Rng::seed_from_u64(100 * seed + 10 * width as u64 + depth as u64);
            let ccl = random_ccl(&mut rng, width, depth);
            assert_eq!(ccl, load(format!("{}", ccl)))
        }
        #[rstest]
        fn test_stress_roundtrip() {
            let ccl = stress_model!();
            assert_eq!(ccl, load(format!("{}", ccl)))
        }

        #[rstest]
        fn test_associative(
            #[values(0, 1, 2, 3, 4, 5, 6, 7, 8, 9)] seed: u64,
            #[values(4, 5, 6)] width: usize,
            #[values(1, 4, 8)] depth: usize,
        ) {
            let mut rng =
                ChaCha8Rng::seed_from_u64(1000 + 100 * seed + 10 * width as u64 + depth as u64);
            let ccl1 = random_ccl(&mut rng, width, depth);
            let ccl2 = random_ccl(&mut rng, width, depth);
            let ccl3 = random_ccl(&mut rng, width, depth);
            assert_eq!(
                Model::merge(ccl1.clone(), Model::merge(ccl2.clone(), ccl3.clone())),
                Model::merge(Model::merge(ccl1, ccl2), ccl3)
            );
        }
        #[rstest]
        fn test_left_empty(
            #[values(1, 2, 3)] seed: u64,
            #[values(4, 5, 6)] width: usize,
            #[values(1, 4, 8)] depth: usize,
        ) {
            let mut rng =
                ChaCha8Rng::seed_from_u64(2000 + 100 * seed + 10 * width as u64 + depth as u64);
            let ccl = random_ccl(&mut rng, width, depth);
            assert_eq!(ccl.clone(), Model::merge(Model::empty(), ccl));
        }
        #[rstest]
        fn test_right_empty(
            #[values(1, 2, 3)] seed: u64,
            #[values(4, 5, 6)] width: usize,
            #[values(1, 4, 8)] depth: usize,
        ) {
            let mut rng =
                ChaCha8Rng::seed_from_u64(3000 + 100 * seed + 10 * width as u64 + depth as u64);
            let ccl = random_ccl(&mut rng, width, depth);
            assert_eq!(ccl.clone(), Model::merge(ccl, Model::empty()));
        }
        #[rstest]
        fn test_split_into_length_one(
            #[values(1, 2, 3)] seed: u64,
            #[values(4, 5, 6)] width: usize,
            #[values(1, 4, 8)] depth: usize,
        ) {
            let mut rng =
                ChaCha8Rng::seed_from_u64(4000 + 100 * seed + 10 * width as u64 + depth as u64);
            let ccl = random_ccl(&mut rng, width, depth);
            assert!(ccl.split().all(|m| m.len() == 1));
        }
        #[rstest]
        fn test_split_merge(
            #[values(1, 2, 3)] seed: u64,
            #[values(4, 5, 6)] width: usize,
            #[values(1, 4, 8)] depth: usize,
        ) {
            let mut rng =
                ChaCha8Rng::seed_from_u64(5000 + 100 * seed + 10 * width as u64 + depth as u64);
            let ccl = random_ccl(&mut rng, width, depth);
            assert_eq!(ccl.split().fold(Model::empty(), Model::merge), ccl.clone());
        }
        #[rstest]
        fn test_fold_endomorphism(
            #[values(1, 2, 3)] seed: u64,
            #[values(4, 5, 6)] width: usize,
            #[values(1, 4, 8)] depth: usize,
        ) {
            let mut rng =
                ChaCha8Rng::seed_from_u64(6000 + 100 * seed + 10 * width as u64 + depth as u64);
            let ccl1 = random_ccl(&mut rng, width, depth);
            let ccl2 = random_ccl(&mut rng, width, depth);
            assert_eq!(
                Model::merge(ccl1.clone(), ccl2.clone()).fold(),
                Model::merge(ccl1.fold(), ccl2.fold())
            );
        }
    }
    mod test_helpers {
        use super::*;
        use pretty_assertions::assert_eq;
        #[test]
        fn test_fold_empty() {
            assert_eq!(Model::empty().clone().fold(), Model::empty())
        }
        #[test]
        fn test_fold_singleton() {
            assert_eq!(model!["key"].fold(), model!["key"])
        }
        #[test]
        fn test_fold() {
            assert_eq!(
                model![
                    "key1" => model!["value1", "key2" => model!["value2"]],
                    "key3" => model!["key2" => model![ "value3" ]]
                ]
                .fold(),
                model![
                    "value1" => model![ "key1" ] ,
                    "key2" => model!["value2" => model![ "key1" ] , "value3" => model![ "key3" ]]
                ],
            )
        }
        #[test]
        fn test_singleton() {
            assert!(Model::singleton("value".to_owned()).is_singleton());
            assert_eq!(
                Model::singleton("value".to_owned()).as_singleton(),
                Some("value")
            );
            assert_eq!(Model::singleton("value".to_owned()), model!["value"]);
        }
    }
}
