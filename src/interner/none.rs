pub type InternedString = String;
pub type InternedStringRef<'a> = &'a str;

pub fn get<S: ToString>(value: S) -> InternedString {
    value.to_string()
}

pub fn try_get(value: &str) -> Option<&str> {
    Some(value)
}

pub fn resolve_ref(key: InternedStringRef) -> &str {
    key
}
