pub mod number;
pub mod string;

use crate::json::number::*;
use crate::json::string::*;

fn is_ws(b: u8) -> bool {
    b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D
}

pub fn skip_ws(s: &[u8], i: usize) -> usize {
    let mut j = i;
    while j < s.len() && is_ws(s[j]) {
        j += 1;
    }
    j
}

pub struct Member {
    pub key: Vec<u8>,
    pub value: usize,
}

pub enum JsonNode {
    Null,
    Bool(bool),
    Number(Number),
    String(Vec<u8>),
    Array(Vec<usize>),
    Object(Vec<Member>),
}

pub struct JsonDoc {
    pub nodes: Vec<JsonNode>,
    pub root: usize,
}

pub const MAX_DEPTH: usize = 128;

fn parse_literal(s: &[u8], i: usize, lit: &[u8]) -> Option<usize> {
    if i >= s.len() || s.len() - i < lit.len() {
        return None;
    }
    let mut k = 0;
    while k < lit.len() {
        if s[i + k] != lit[k] {
            return None;
        }
        k += 1;
    }
    Some(i + lit.len())
}

fn parse_scalar(s: &[u8], i: usize) -> Option<(JsonNode, usize)> {
    let c = s[i];
    if c == b'"' {
        match parse_string(s, i + 1) {
            Some((v, j)) => Some((JsonNode::String(v), j)),
            None => None,
        }
    } else if c == b't' {
        match parse_literal(s, i, &[b't', b'r', b'u', b'e']) {
            Some(j) => Some((JsonNode::Bool(true), j)),
            None => None,
        }
    } else if c == b'f' {
        match parse_literal(s, i, &[b'f', b'a', b'l', b's', b'e']) {
            Some(j) => Some((JsonNode::Bool(false), j)),
            None => None,
        }
    } else if c == b'n' {
        match parse_literal(s, i, &[b'n', b'u', b'l', b'l']) {
            Some(j) => Some((JsonNode::Null, j)),
            None => None,
        }
    } else if c == b'-' || is_digit(c) {
        match parse_number(s, i) {
            Some((n, j)) => Some((JsonNode::Number(n), j)),
            None => None,
        }
    } else {
        None
    }
}

fn parse_value(s: &[u8], i: usize, depth: usize, nodes: &mut Vec<JsonNode>) -> Option<(usize, usize)> {
    if i >= s.len() {
        return None;
    }
    let c = s[i];
    if c == b'[' {
        if depth == 0 {
            return None;
        }
        let mut items: Vec<usize> = Vec::new();
        let mut j = skip_ws(s, i + 1);
        if j < s.len() && s[j] == b']' {
            nodes.push(JsonNode::Array(items));
            return Some((nodes.len() - 1, j + 1));
        }
        loop {
            match parse_value(s, j, depth - 1, nodes) {
                None => return None,
                Some((id, k)) => {
                    items.push(id);
                    j = skip_ws(s, k);
                }
            }
            if j >= s.len() {
                return None;
            }
            if s[j] == b',' {
                j = skip_ws(s, j + 1);
            } else if s[j] == b']' {
                nodes.push(JsonNode::Array(items));
                return Some((nodes.len() - 1, j + 1));
            } else {
                return None;
            }
        }
    } else if c == b'{' {
        if depth == 0 {
            return None;
        }
        let mut members: Vec<Member> = Vec::new();
        let mut j = skip_ws(s, i + 1);
        if j < s.len() && s[j] == b'}' {
            nodes.push(JsonNode::Object(members));
            return Some((nodes.len() - 1, j + 1));
        }
        loop {
            if j >= s.len() || s[j] != b'"' {
                return None;
            }
            let key = match parse_string(s, j + 1) {
                None => return None,
                Some((k, e)) => {
                    j = skip_ws(s, e);
                    k
                }
            };
            if j >= s.len() || s[j] != b':' {
                return None;
            }
            j = skip_ws(s, j + 1);
            match parse_value(s, j, depth - 1, nodes) {
                None => return None,
                Some((id, k)) => {
                    members.push(Member { key, value: id });
                    j = skip_ws(s, k);
                }
            }
            if j >= s.len() {
                return None;
            }
            if s[j] == b',' {
                j = skip_ws(s, j + 1);
            } else if s[j] == b'}' {
                nodes.push(JsonNode::Object(members));
                return Some((nodes.len() - 1, j + 1));
            } else {
                return None;
            }
        }
    } else {
        match parse_scalar(s, i) {
            None => None,
            Some((node, j)) => {
                nodes.push(node);
                Some((nodes.len() - 1, j))
            }
        }
    }
}

pub fn parse_json(s: &[u8]) -> Option<JsonDoc> {
    let mut i = 0;
    if s.len() >= 3 && s[0] == 0xEF && s[1] == 0xBB && s[2] == 0xBF {
        i = 3;
    }
    i = skip_ws(s, i);
    let mut nodes: Vec<JsonNode> = Vec::new();
    match parse_value(s, i, MAX_DEPTH, &mut nodes) {
        None => None,
        Some((root, j)) => {
            if skip_ws(s, j) == s.len() {
                Some(JsonDoc { nodes, root })
            } else {
                None
            }
        }
    }
}
