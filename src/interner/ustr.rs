use std::fmt::Display;

// We wrap this so we can make it not copy
#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct InternedString(ustr::Ustr);
impl InternedString {
    pub fn as_ref(&self) -> InternedStringRef {
        self
    }
}
impl Display for InternedString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub type InternedStringRef<'a> = &'a InternedString;

pub fn get<S: ToString>(value: S) -> InternedString {
    InternedString(ustr::ustr(&value.to_string()))
}

pub fn try_get(value: &str) -> Option<InternedString> {
    ustr::existing_ustr(value).map(InternedString)
}

pub fn resolve(key: InternedStringRef) -> String {
    key.0.to_string()
}

pub fn resolve_ref(key: InternedStringRef) -> &str {
    key.0.as_str()
}
