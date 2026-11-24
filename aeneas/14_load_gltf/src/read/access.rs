use crate::json::*;
use crate::json::number::*;
use crate::model::*;

pub fn is_last_member(obj: &Vec<Member>, i: usize) -> bool {
    match find_member(obj, &obj[i].key) {
        None => false,
        Some(k) => k == i,
    }
}

pub fn find_member(obj: &Vec<Member>, key: &[u8]) -> Option<usize> {
    let mut found: Option<usize> = None;
    let mut i = 0;
    while i < obj.len() {
        if bytes_eq(&obj[i].key, key) {
            found = Some(i);
        }
        i += 1;
    }
    found
}

pub fn node_at(d: &Vec<JsonNode>, id: usize) -> Option<&JsonNode> {
    if id < d.len() {
        Some(&d[id])
    } else {
        None
    }
}

fn member_node<'a>(d: &'a Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<&'a JsonNode>, ()> {
    match find_member(obj, key) {
        None => Ok(None),
        Some(i) => match node_at(d, obj[i].value) {
            None => Err(()),
            Some(n) => Ok(Some(n)),
        },
    }
}

pub fn get_uint(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<u64>, ()> {
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(JsonNode::Number(n))) => match number_to_u64(n) {
            Some(v) => Ok(Some(v)),
            None => Err(()),
        },
        Ok(Some(_)) => Err(()),
    }
}

pub fn get_bool(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<bool>, ()> {
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(JsonNode::Bool(b))) => Ok(Some(*b)),
        Ok(Some(_)) => Err(()),
    }
}

fn copy_bytes(v: &Vec<u8>) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < v.len() {
        out.push(v[i]);
        i += 1;
    }
    out
}

pub fn get_string(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<Vec<u8>>, ()> {
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(JsonNode::String(s))) => Ok(Some(copy_bytes(s))),
        Ok(Some(_)) => Err(()),
    }
}

pub fn get_object<'a>(d: &'a Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<&'a Vec<Member>>, ()> {
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(JsonNode::Object(m))) => Ok(Some(m)),
        Ok(Some(_)) => Err(()),
    }
}

pub fn get_array<'a>(d: &'a Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<&'a Vec<usize>>, ()> {
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(JsonNode::Array(a))) => {
            if a.len() == 0 {
                Err(())
            } else {
                Ok(Some(a))
            }
        }
        Ok(Some(_)) => Err(()),
    }
}

fn uints_of(d: &Vec<JsonNode>, a: &Vec<usize>) -> Option<Vec<u64>> {
    let mut out: Vec<u64> = Vec::new();
    let mut i = 0;
    while i < a.len() {
        match node_at(d, a[i]) {
            Some(JsonNode::Number(n)) => match number_to_u64(n) {
                Some(v) => out.push(v),
                None => return None,
            },
            _ => return None,
        }
        i += 1;
    }
    Some(out)
}

pub fn get_uint_array(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<Vec<u64>>, ()> {
    match get_array(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(a)) => match uints_of(d, a) {
            None => Err(()),
            Some(v) => Ok(Some(v)),
        },
    }
}

fn all_numbers(d: &Vec<JsonNode>, a: &Vec<usize>) -> bool {
    let mut i = 0;
    while i < a.len() {
        match node_at(d, a[i]) {
            Some(JsonNode::Number(_)) => {}
            _ => return false,
        }
        i += 1;
    }
    true
}

pub fn get_number_array_len(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<Option<u64>, ()> {
    match get_array(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(None),
        Ok(Some(a)) => {
            if all_numbers(d, a) {
                Ok(Some(a.len() as u64))
            } else {
                Err(())
            }
        }
    }
}

pub fn check_number(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8]) -> Result<bool, ()> {
    match member_node(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(false),
        Ok(Some(JsonNode::Number(_))) => Ok(true),
        Ok(Some(_)) => Err(()),
    }
}

pub fn check_number_array(d: &Vec<JsonNode>, obj: &Vec<Member>, key: &[u8], len: u64) -> Result<bool, ()> {
    match get_number_array_len(d, obj, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(false),
        Ok(Some(n)) => {
            if n == len {
                Ok(true)
            } else {
                Err(())
            }
        }
    }
}

pub fn as_object(d: &Vec<JsonNode>, id: usize) -> Result<&Vec<Member>, ()> {
    match node_at(d, id) {
        Some(JsonNode::Object(m)) => Ok(m),
        _ => Err(()),
    }
}

pub(crate) fn check_extensions(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<(), ()> {
    match get_object(d, o, &[b'e', b'x', b't', b'e', b'n', b's', b'i', b'o', b'n', b's']) {
        Err(()) => Err(()),
        Ok(None) => Ok(()),
        Ok(Some(e)) => collect_extension_names(d, e, ext),
    }
}

fn collect_extension_names(d: &Vec<JsonNode>, e: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<(), ()> {
    let mut i = 0;
    while i < e.len() {
        if is_last_member(e, i) {
            match node_at(d, e[i].value) {
                Some(JsonNode::Object(_)) => ext.push(copy_key(&e[i].key)),
                _ => return Err(()),
            }
        }
        i += 1;
    }
    Ok(())
}

pub(crate) fn check_child_of_root(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<(), ()> {
    match get_string(d, o, &[b'n', b'a', b'm', b'e']) {
        Err(()) => return Err(()),
        Ok(_) => {}
    }
    check_extensions(d, o, ext)
}

pub(crate) fn req_uint(d: &Vec<JsonNode>, o: &Vec<Member>, key: &[u8]) -> Result<u64, ()> {
    match get_uint(d, o, key) {
        Ok(Some(v)) => Ok(v),
        _ => Err(()),
    }
}

pub(crate) fn copy_key(v: &Vec<u8>) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < v.len() {
        out.push(v[i]);
        i += 1;
    }
    out
}
