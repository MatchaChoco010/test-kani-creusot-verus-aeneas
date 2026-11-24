use crate::model::*;
use crate::validate::mesh::*;

fn base64_char(b: u8) -> bool {
    (b >= b'A' && b <= b'Z') || (b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') || b == b'+' || b == b'/'
}

fn hex_digit(b: u8) -> bool {
    (b >= b'0' && b <= b'9') || (b >= b'A' && b <= b'F') || (b >= b'a' && b <= b'f')
}

fn range_eq(s: &Vec<u8>, start: usize, end: usize, lit: &[u8]) -> bool {
    if end - start != lit.len() {
        return false;
    }
    let mut i = 0;
    while i < lit.len() {
        if s[start + i] != lit[i] {
            return false;
        }
        i += 1;
    }
    true
}

fn is_alpha(b: u8) -> bool {
    (b >= b'A' && b <= b'Z') || (b >= b'a' && b <= b'z')
}

fn find_scheme_end(uri: &Vec<u8>) -> usize {
    let mut i = 0;
    while i < uri.len() {
        let c = uri[i];
        if c == b':' {
            return i;
        }
        if c == b'/' || c == b'?' || c == b'#' {
            return uri.len();
        }
        i += 1;
    }
    uri.len()
}

fn scheme_chars_ok(uri: &Vec<u8>, end: usize) -> bool {
    let mut k = 1;
    while k < end {
        let c = uri[k];
        if !(is_alpha(c) || (c >= b'0' && c <= b'9') || c == b'+' || c == b'-' || c == b'.') {
            return false;
        }
        k += 1;
    }
    true
}

fn uri_chars_ok(uri: &Vec<u8>) -> bool {
    let mut fragment = false;
    let mut i = 0;
    while i < uri.len() {
        let c = uri[i];
        if c <= 0x20 || c == 0x7F || c == b'"' || c == b'<' || c == b'>' || c == b'\\' || c == b'^' || c == b'`' || c == b'{' || c == b'|' || c == b'}' {
            return false;
        }
        if c == b'#' {
            if fragment {
                return false;
            }
            fragment = true;
        }
        if c == b'%' && (uri.len() - i < 3 || !hex_digit(uri[i + 1]) || !hex_digit(uri[i + 2])) {
            return false;
        }
        i += 1;
    }
    true
}

pub fn uri_syntax_ok(uri: &Vec<u8>) -> bool {
    let end = find_scheme_end(uri);
    let scheme_ok = end == uri.len() || (end > 0 && is_alpha(uri[0]) && scheme_chars_ok(uri, end));
    scheme_ok && uri_chars_ok(uri)
}

pub struct DataUri {
    pub media_end: usize,
    pub length: u64,
}

pub fn is_data_uri(uri: &Vec<u8>) -> bool {
    starts_with(uri, &[b'd', b'a', b't', b'a', b':'])
}

fn find_byte(s: &Vec<u8>, from: usize, to: usize, b: u8) -> usize {
    let mut i = from;
    while i < to {
        if s[i] == b {
            return i;
        }
        i += 1;
    }
    to
}

fn parameter_ok(uri: &Vec<u8>, start: usize, end: usize) -> bool {
    let eq = find_byte(uri, start, end, b'=');
    eq > start && eq < end
}

fn parameters(uri: &Vec<u8>, from: usize, comma: usize) -> Option<bool> {
    let mut seg = from;
    while seg < comma {
        let start = seg + 1;
        let end = find_byte(uri, start, comma, b';');
        if end == comma && range_eq(uri, start, end, &[b'b', b'a', b's', b'e', b'6', b'4']) {
            return Some(true);
        }
        if !parameter_ok(uri, start, end) {
            return None;
        }
        seg = end;
    }
    Some(false)
}

fn base64_chars_ok(uri: &Vec<u8>, start: usize, end: usize) -> bool {
    let mut i = start;
    while i < end {
        if !base64_char(uri[i]) {
            return false;
        }
        i += 1;
    }
    true
}

fn base64_length(uri: &Vec<u8>, start: usize) -> Option<u64> {
    let n = uri.len() - start;
    if n % 4 != 0 {
        return None;
    }
    let pad = if n > 0 && uri[uri.len() - 1] == b'=' {
        if uri[uri.len() - 2] == b'=' { 2 } else { 1 }
    } else {
        0
    };
    if base64_chars_ok(uri, start, uri.len() - pad) {
        Some((n / 4 * 3 - pad) as u64)
    } else {
        None
    }
}

fn percent_length(uri: &Vec<u8>, start: usize) -> Option<u64> {
    let mut len: u64 = 0;
    let mut i = start;
    while i < uri.len() {
        if uri[i] == b'%' {
            if uri.len() - i < 3 || !hex_digit(uri[i + 1]) || !hex_digit(uri[i + 2]) {
                return None;
            }
            i += 3;
        } else {
            i += 1;
        }
        len += 1;
    }
    Some(len)
}

pub fn parse_data_uri(uri: &Vec<u8>) -> Option<DataUri> {
    let comma = find_byte(uri, 5, uri.len(), b',');
    if comma >= uri.len() {
        return None;
    }
    let media_end = find_byte(uri, 5, comma, b';');
    let length = match parameters(uri, media_end, comma) {
        None => None,
        Some(true) => base64_length(uri, comma + 1),
        Some(false) => percent_length(uri, comma + 1),
    };
    match length {
        None => None,
        Some(length) => Some(DataUri { media_end, length }),
    }
}

fn buffer_media_type_ok(uri: &Vec<u8>, media_end: usize) -> bool {
    range_eq(uri, 5, media_end, &[b'a', b'p', b'p', b'l', b'i', b'c', b'a', b't', b'i', b'o', b'n', b'/', b'o', b'c', b't', b'e', b't', b'-', b's', b't', b'r', b'e', b'a', b'm'])
        || range_eq(uri, 5, media_end, &[b'a', b'p', b'p', b'l', b'i', b'c', b'a', b't', b'i', b'o', b'n', b'/', b'g', b'l', b't', b'f', b'-', b'b', b'u', b'f', b'f', b'e', b'r'])
}

fn buffer_uri_ok(uri: &Vec<u8>, byte_length: u64) -> bool {
    if !uri_syntax_ok(uri) {
        false
    } else if !is_data_uri(uri) {
        true
    } else {
        match parse_data_uri(uri) {
            None => false,
            Some(d) => buffer_media_type_ok(uri, d.media_end) && d.length >= byte_length,
        }
    }
}

fn image_uri_ok(uri: &Vec<u8>) -> bool {
    uri_syntax_ok(uri) && (!is_data_uri(uri) || parse_data_uri(uri).is_some())
}

fn buffer_ok(g: &Gltf, b: usize) -> bool {
    let buf = &g.buffers[b];
    if buf.byte_length == 0 {
        return false;
    }
    match &buf.uri {
        None => {
            if b == 0 && g.is_glb {
                match g.glb_bin_len {
                    None => false,
                    Some(n) => n >= buf.byte_length,
                }
            } else {
                true
            }
        }
        Some(u) => buffer_uri_ok(u, buf.byte_length),
    }
}

pub(crate) fn buffers_ok(g: &Gltf) -> bool {
    let mut b = 0;
    while b < g.buffers.len() {
        if !buffer_ok(g, b) {
            return false;
        }
        b += 1;
    }
    true
}

fn image_ok(im: &Image) -> bool {
    let uri_ok = match &im.uri {
        None => true,
        Some(u) => image_uri_ok(u),
    };
    im.uri.is_some() != im.buffer_view.is_some() && (im.buffer_view.is_none() || im.has_mime_type) && uri_ok
}

pub(crate) fn images_ok(g: &Gltf) -> bool {
    let mut i = 0;
    while i < g.images.len() {
        if !image_ok(&g.images[i]) {
            return false;
        }
        i += 1;
    }
    true
}
