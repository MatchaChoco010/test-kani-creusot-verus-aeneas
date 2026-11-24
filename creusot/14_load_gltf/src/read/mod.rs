pub mod access;
pub mod objects;

use creusot_std::prelude::*;
use crate::json::*;
use crate::model::*;
use crate::read::access::*;
use crate::read::objects::*;

#[logic(open)]
pub fn all_strings(l: JList) -> bool {
    pearlite! { forall<t> 0 <= t && t < jlen(l) ==> match nth(l, t) { JsonS::Str(_) => true, _ => false } }
}

#[logic(open)]
pub fn strings_is(l: JList, v: Seq<Vec<u8>>) -> bool {
    pearlite! { jlen(l) == v.len() && forall<t> 0 <= t && t < v.len() ==> nth(l, t) == JsonS::Str(v[t]@) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result { Ok(v) => strings_is(list_of(d@, a@), v@), Err(()) => !all_strings(list_of(d@, a@)) })]
#[check(terminates)]
fn strings_of(d: &Vec<JsonNode>, a: &Vec<usize>) -> Result<Vec<Vec<u8>>, ()> {
    snapshot!(lemma_list_index(d@, a@));
    snapshot!(lemma_tree_node(d@, 0));
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> tree(d@, a@[t]@) == JsonS::Str(out@[t]@))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        match node_at(d, a[i]) {
            Some(JsonNode::String(s)) => out.push(copy_key(s)),
            _ => return Err(()),
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open, inline)]
pub fn f_string_array(o: JObj, k: Seq<u8>, v: Seq<Vec<u8>>) -> bool {
    pearlite! {
        match p_array(o, k) { Err(()) => false, Ok(None) => v.len() == 0, Ok(Some(l)) => strings_is(l, v) }
    }
}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(forall<k: Seq<u8>> #[trigger(p_array(obj_of(d@, o@), k))] seq_is(k, key@) ==> match result { Ok(v) => f_string_array(obj_of(d@, o@), k, v@), Err(()) => forall<v: Seq<Vec<u8>>> !f_string_array(obj_of(d@, o@), k, v) })]
#[ensures(forall<k: Seq<u8>> #[trigger(p_array(obj_of(d@, o@), k))] seq_is(k, key@) ==> match result { Ok(v) => match p_array(obj_of(d@, o@), k) { Err(()) => false, Ok(None) => v@.len() == 0, Ok(Some(l)) => strings_is(l, v@) }, Err(()) => match p_array(obj_of(d@, o@), k) { Err(()) => true, Ok(None) => false, Ok(Some(l)) => !all_strings(l) } })]
#[check(terminates)]
fn read_string_array(d: &Vec<JsonNode>, o: &Vec<Member>, key: &[u8]) -> Result<Vec<Vec<u8>>, ()> {
    snapshot!(lemma_seq_is_eq(key@, key@));
    match get_array(d, o, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => strings_of(d, a),
    }
}

#[logic(open)]
pub fn rd_scene(j: JsonS, x: Scene) -> bool {
    pearlite! { is_object(j) && rd_scene_o(obj_or_nil(j), x) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && (forall<t> 0 <= t && t < v@.len() ==> rd_scene(nth(list_of(d@, a@), t), v@[t]))
        && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_obj(nth(list_of(d@, a@), t), x))),
    Err(e) => e == GltfError::Invalid && exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: Scene> !rd_scene(nth(list_of(d@, a@), t), y),
})]
#[check(terminates)]
fn read_scenes_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Scene>, GltfError> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<Scene> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_scene(tree(d@, a@[t]@), out@[t]))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_obj(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        proof_assert!(nth(list_of(d@, a@), i@) == tree(d@, a@[i@]@));
        proof_assert!(forall<y: Scene> rd_scene(tree(d@, a@[i@]@), y) == (is_object(tree(d@, a@[i@]@)) && rd_scene_o(obj_or_nil(tree(d@, a@[i@]@)), y)));
        match read_scene(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

// 配列プロパティの各要素を読む（なければ空）
#[logic(open)]
pub fn rd_a_scenes(o: JObj, v: Seq<Scene>) -> bool {
    pearlite! {
        match p_array(o, key_scenes()) {
            Err(()) => false,
            Ok(None) => v.len() == 0,
            Ok(Some(l)) => jlen(l) == v.len() && forall<t> 0 <= t && t < v.len() ==> rd_scene(nth(l, t), v[t]),
        }
    }
}

#[logic(open)]
pub fn ext_a_scenes(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        match p_array(o, key_scenes()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_obj(nth(l, t), x), _ => false }
    }
}

#[logic(open)]
pub fn key_scenes() -> Seq<u8> {
    pearlite! { seq![115u8, 99u8, 101u8, 110u8, 101u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 6 && s[0] == 115u8 && s[1] == 99u8 && s[2] == 101u8 && s[3] == 110u8 && s[4] == 101u8 && s[5] == 115u8 ==> seq_is(key_scenes(), s))]
pub fn lemma_key_scenes(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(v) => rd_a_scenes(obj_of(d@, o@), v@) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_a_scenes(obj_of(d@, o@), x))),
    Err(e) => e == GltfError::Invalid && forall<v: Seq<Scene>> !rd_a_scenes(obj_of(d@, o@), v),
})]
#[check(terminates)]
fn read_scenes(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Scene>, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_scenes(Seq::empty()));
    match get_array(d, o, &[b's', b'c', b'e', b'n', b'e', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_scenes_items(d, a, ext),
    }
}

#[logic(open)]
pub fn rd_node(j: JsonS, x: Node) -> bool {
    pearlite! { is_object(j) && rd_node_o(obj_or_nil(j), x) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && (forall<t> 0 <= t && t < v@.len() ==> rd_node(nth(list_of(d@, a@), t), v@[t]))
        && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_obj(nth(list_of(d@, a@), t), x))),
    Err(e) => e == GltfError::Invalid && exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: Node> !rd_node(nth(list_of(d@, a@), t), y),
})]
#[check(terminates)]
fn read_nodes_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Node>, GltfError> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<Node> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_node(tree(d@, a@[t]@), out@[t]))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_obj(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        proof_assert!(nth(list_of(d@, a@), i@) == tree(d@, a@[i@]@));
        proof_assert!(forall<y: Node> rd_node(tree(d@, a@[i@]@), y) == (is_object(tree(d@, a@[i@]@)) && rd_node_o(obj_or_nil(tree(d@, a@[i@]@)), y)));
        match read_node(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open)]
pub fn rd_a_nodes(o: JObj, v: Seq<Node>) -> bool {
    pearlite! {
        match p_array(o, key_nodes()) {
            Err(()) => false,
            Ok(None) => v.len() == 0,
            Ok(Some(l)) => jlen(l) == v.len() && forall<t> 0 <= t && t < v.len() ==> rd_node(nth(l, t), v[t]),
        }
    }
}

#[logic(open)]
pub fn ext_a_nodes(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        match p_array(o, key_nodes()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_obj(nth(l, t), x), _ => false }
    }
}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(v) => rd_a_nodes(obj_of(d@, o@), v@) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_a_nodes(obj_of(d@, o@), x))),
    Err(e) => e == GltfError::Invalid && forall<v: Seq<Node>> !rd_a_nodes(obj_of(d@, o@), v),
})]
#[check(terminates)]
fn read_nodes(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Node>, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_nodes(Seq::empty()));
    match get_array(d, o, &[b'n', b'o', b'd', b'e', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_nodes_items(d, a, ext),
    }
}

#[logic(open)]
pub fn rd_mesh(j: JsonS, x: Mesh) -> bool {
    pearlite! { is_object(j) && rd_mesh_o(obj_or_nil(j), x) }
}

#[logic(open)]
pub fn ext_mesh(j: JsonS, x: Seq<u8>) -> bool {
    pearlite! { is_object(j) && ext_mesh_o(obj_or_nil(j), x) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && (forall<t> 0 <= t && t < v@.len() ==> rd_mesh(nth(list_of(d@, a@), t), v@[t]))
        && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_mesh(nth(list_of(d@, a@), t), x))),
    Err(e) => e == GltfError::Invalid && exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: Mesh> !rd_mesh(nth(list_of(d@, a@), t), y),
})]
#[check(terminates)]
fn read_meshes_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Mesh>, GltfError> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<Mesh> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_mesh(tree(d@, a@[t]@), out@[t]))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_mesh(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        proof_assert!(nth(list_of(d@, a@), i@) == tree(d@, a@[i@]@));
        proof_assert!(forall<y: Mesh> rd_mesh(tree(d@, a@[i@]@), y) == (is_object(tree(d@, a@[i@]@)) && rd_mesh_o(obj_or_nil(tree(d@, a@[i@]@)), y)));
        match read_mesh(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open)]
pub fn rd_a_meshes(o: JObj, v: Seq<Mesh>) -> bool {
    pearlite! {
        match p_array(o, key_meshes()) {
            Err(()) => false,
            Ok(None) => v.len() == 0,
            Ok(Some(l)) => jlen(l) == v.len() && forall<t> 0 <= t && t < v.len() ==> rd_mesh(nth(l, t), v[t]),
        }
    }
}

#[logic(open)]
pub fn ext_a_meshes(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        match p_array(o, key_meshes()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_mesh(nth(l, t), x), _ => false }
    }
}

#[logic(open)]
pub fn key_meshes() -> Seq<u8> {
    pearlite! { seq![109u8, 101u8, 115u8, 104u8, 101u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 6 && s[0] == 109u8 && s[1] == 101u8 && s[2] == 115u8 && s[3] == 104u8 && s[4] == 101u8 && s[5] == 115u8 ==> seq_is(key_meshes(), s))]
pub fn lemma_key_meshes(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(v) => rd_a_meshes(obj_of(d@, o@), v@) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_a_meshes(obj_of(d@, o@), x))),
    Err(e) => e == GltfError::Invalid && forall<v: Seq<Mesh>> !rd_a_meshes(obj_of(d@, o@), v),
})]
#[check(terminates)]
fn read_meshes(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Mesh>, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_meshes(Seq::empty()));
    match get_array(d, o, &[b'm', b'e', b's', b'h', b'e', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_meshes_items(d, a, ext),
    }
}

// strict = false のときは (U) の場合（未知の type）を受け入れる
#[logic(open)]
pub fn rd_accessor(j: JsonS, x: Accessor, strict: bool) -> bool {
    pearlite! { is_object(j) && rd_accessor_o(obj_or_nil(j), x, strict) }
}

#[logic(open)]
pub fn ext_accessor(j: JsonS, x: Seq<u8>) -> bool {
    pearlite! { is_object(j) && ext_accessor_o(obj_or_nil(j), x) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && (forall<t> 0 <= t && t < v@.len() ==> rd_accessor(nth(list_of(d@, a@), t), v@[t], true))
        && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_accessor(nth(list_of(d@, a@), t), x))),
    Err(e) => (exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: Accessor> !rd_accessor(nth(list_of(d@, a@), t), y, true))
        && (e == GltfError::Invalid ==> exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: Accessor> !rd_accessor(nth(list_of(d@, a@), t), y, false))
        && (e == GltfError::Unsupported ==> exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && unsup_accessor(nth(list_of(d@, a@), t)))
        && (e == GltfError::Invalid || e == GltfError::Unsupported),
})]
#[check(terminates)]
fn read_accessors_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Accessor>, GltfError> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<Accessor> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_accessor(tree(d@, a@[t]@), out@[t], true))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_accessor(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        proof_assert!(nth(list_of(d@, a@), i@) == tree(d@, a@[i@]@));
        proof_assert!(forall<y: Accessor> rd_accessor(tree(d@, a@[i@]@), y, true) == (is_object(tree(d@, a@[i@]@)) && rd_accessor_o(obj_or_nil(tree(d@, a@[i@]@)), y, true)));
        match read_accessor(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(e) => return Err(e),
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open)]
pub fn rd_a_accessors(o: JObj, v: Seq<Accessor>, strict: bool) -> bool {
    pearlite! {
        match p_array(o, key_accessors()) {
            Err(()) => false,
            Ok(None) => v.len() == 0,
            Ok(Some(l)) => jlen(l) == v.len() && forall<t> 0 <= t && t < v.len() ==> rd_accessor(nth(l, t), v[t], strict),
        }
    }
}

#[logic(open)]
pub fn ext_a_accessors(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        match p_array(o, key_accessors()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_accessor(nth(l, t), x), _ => false }
    }
}

#[logic(open)]
pub fn unsup_a_accessors(o: JObj) -> bool {
    pearlite! {
        match p_array(o, key_accessors()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && unsup_accessor(nth(l, t)), _ => false }
    }
}

#[logic(open)]
pub fn key_accessors() -> Seq<u8> {
    pearlite! { seq![97u8, 99u8, 99u8, 101u8, 115u8, 115u8, 111u8, 114u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 9 && s[0] == 97u8 && s[1] == 99u8 && s[2] == 99u8 && s[3] == 101u8 && s[4] == 115u8 && s[5] == 115u8 && s[6] == 111u8 && s[7] == 114u8 && s[8] == 115u8 ==> seq_is(key_accessors(), s))]
pub fn lemma_key_accessors(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(v) => rd_a_accessors(obj_of(d@, o@), v@, true) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_a_accessors(obj_of(d@, o@), x))),
    Err(e) => (forall<v: Seq<Accessor>> !rd_a_accessors(obj_of(d@, o@), v, true))
        && (e == GltfError::Invalid ==> forall<v: Seq<Accessor>> !rd_a_accessors(obj_of(d@, o@), v, false))
        && (e == GltfError::Unsupported ==> unsup_a_accessors(obj_of(d@, o@)))
        && (e == GltfError::Invalid || e == GltfError::Unsupported),
})]
#[check(terminates)]
fn read_accessors(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Accessor>, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_accessors(Seq::empty()));
    match get_array(d, o, &[b'a', b'c', b'c', b'e', b's', b's', b'o', b'r', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_accessors_items(d, a, ext),
    }
}

#[logic(open)]
pub fn rd_buffer_view(j: JsonS, x: BufferView) -> bool {
    pearlite! { is_object(j) && rd_buffer_view_o(obj_or_nil(j), x) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && (forall<t> 0 <= t && t < v@.len() ==> rd_buffer_view(nth(list_of(d@, a@), t), v@[t]))
        && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_obj(nth(list_of(d@, a@), t), x))),
    Err(e) => e == GltfError::Invalid && exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: BufferView> !rd_buffer_view(nth(list_of(d@, a@), t), y),
})]
#[check(terminates)]
fn read_buffer_views_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<BufferView>, GltfError> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<BufferView> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_buffer_view(tree(d@, a@[t]@), out@[t]))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_obj(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        proof_assert!(nth(list_of(d@, a@), i@) == tree(d@, a@[i@]@));
        proof_assert!(forall<y: BufferView> rd_buffer_view(tree(d@, a@[i@]@), y) == (is_object(tree(d@, a@[i@]@)) && rd_buffer_view_o(obj_or_nil(tree(d@, a@[i@]@)), y)));
        match read_buffer_view(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open)]
pub fn rd_a_buffer_views(o: JObj, v: Seq<BufferView>) -> bool {
    pearlite! {
        match p_array(o, key_buffer_views()) {
            Err(()) => false,
            Ok(None) => v.len() == 0,
            Ok(Some(l)) => jlen(l) == v.len() && forall<t> 0 <= t && t < v.len() ==> rd_buffer_view(nth(l, t), v[t]),
        }
    }
}

#[logic(open)]
pub fn ext_a_buffer_views(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        match p_array(o, key_buffer_views()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_obj(nth(l, t), x), _ => false }
    }
}

#[logic(open)]
pub fn key_buffer_views() -> Seq<u8> {
    pearlite! { seq![98u8, 117u8, 102u8, 102u8, 101u8, 114u8, 86u8, 105u8, 101u8, 119u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 11 && s[0] == 98u8 && s[1] == 117u8 && s[2] == 102u8 && s[3] == 102u8 && s[4] == 101u8 && s[5] == 114u8 && s[6] == 86u8 && s[7] == 105u8 && s[8] == 101u8 && s[9] == 119u8 && s[10] == 115u8 ==> seq_is(key_buffer_views(), s))]
pub fn lemma_key_buffer_views(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(v) => rd_a_buffer_views(obj_of(d@, o@), v@) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_a_buffer_views(obj_of(d@, o@), x))),
    Err(e) => e == GltfError::Invalid && forall<v: Seq<BufferView>> !rd_a_buffer_views(obj_of(d@, o@), v),
})]
#[check(terminates)]
fn read_buffer_views(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<BufferView>, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_buffer_views(Seq::empty()));
    match get_array(d, o, &[b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_buffer_views_items(d, a, ext),
    }
}

#[logic(open)]
pub fn rd_buffer(j: JsonS, x: Buffer) -> bool {
    pearlite! { is_object(j) && rd_buffer_o(obj_or_nil(j), x) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && (forall<t> 0 <= t && t < v@.len() ==> rd_buffer(nth(list_of(d@, a@), t), v@[t]))
        && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_obj(nth(list_of(d@, a@), t), x))),
    Err(e) => e == GltfError::Invalid && exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: Buffer> !rd_buffer(nth(list_of(d@, a@), t), y),
})]
#[check(terminates)]
fn read_buffers_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Buffer>, GltfError> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<Buffer> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_buffer(tree(d@, a@[t]@), out@[t]))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_obj(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        proof_assert!(nth(list_of(d@, a@), i@) == tree(d@, a@[i@]@));
        proof_assert!(forall<y: Buffer> rd_buffer(tree(d@, a@[i@]@), y) == (is_object(tree(d@, a@[i@]@)) && rd_buffer_o(obj_or_nil(tree(d@, a@[i@]@)), y)));
        match read_buffer(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open)]
pub fn rd_a_buffers(o: JObj, v: Seq<Buffer>) -> bool {
    pearlite! {
        match p_array(o, key_buffers()) {
            Err(()) => false,
            Ok(None) => v.len() == 0,
            Ok(Some(l)) => jlen(l) == v.len() && forall<t> 0 <= t && t < v.len() ==> rd_buffer(nth(l, t), v[t]),
        }
    }
}

#[logic(open)]
pub fn ext_a_buffers(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        match p_array(o, key_buffers()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_obj(nth(l, t), x), _ => false }
    }
}

#[logic(open)]
pub fn key_buffers() -> Seq<u8> {
    pearlite! { seq![98u8, 117u8, 102u8, 102u8, 101u8, 114u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 7 && s[0] == 98u8 && s[1] == 117u8 && s[2] == 102u8 && s[3] == 102u8 && s[4] == 101u8 && s[5] == 114u8 && s[6] == 115u8 ==> seq_is(key_buffers(), s))]
pub fn lemma_key_buffers(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(v) => rd_a_buffers(obj_of(d@, o@), v@) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_a_buffers(obj_of(d@, o@), x))),
    Err(e) => e == GltfError::Invalid && forall<v: Seq<Buffer>> !rd_a_buffers(obj_of(d@, o@), v),
})]
#[check(terminates)]
fn read_buffers(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Buffer>, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_buffers(Seq::empty()));
    match get_array(d, o, &[b'b', b'u', b'f', b'f', b'e', b'r', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_buffers_items(d, a, ext),
    }
}

#[logic(open)]
pub fn rd_material(j: JsonS, x: Material) -> bool {
    pearlite! { is_object(j) && rd_material_o(obj_or_nil(j), x) }
}

#[logic(open)]
pub fn ext_material(j: JsonS, x: Seq<u8>) -> bool {
    pearlite! { is_object(j) && ext_material_o(obj_or_nil(j), x) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && (forall<t> 0 <= t && t < v@.len() ==> rd_material(nth(list_of(d@, a@), t), v@[t]))
        && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_material(nth(list_of(d@, a@), t), x))),
    Err(e) => e == GltfError::Invalid && exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: Material> !rd_material(nth(list_of(d@, a@), t), y),
})]
#[check(terminates)]
fn read_materials_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Material>, GltfError> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<Material> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_material(tree(d@, a@[t]@), out@[t]))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_material(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        proof_assert!(nth(list_of(d@, a@), i@) == tree(d@, a@[i@]@));
        proof_assert!(forall<y: Material> rd_material(tree(d@, a@[i@]@), y) == (is_object(tree(d@, a@[i@]@)) && rd_material_o(obj_or_nil(tree(d@, a@[i@]@)), y)));
        match read_material(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open)]
pub fn rd_a_materials(o: JObj, v: Seq<Material>) -> bool {
    pearlite! {
        match p_array(o, key_materials()) {
            Err(()) => false,
            Ok(None) => v.len() == 0,
            Ok(Some(l)) => jlen(l) == v.len() && forall<t> 0 <= t && t < v.len() ==> rd_material(nth(l, t), v[t]),
        }
    }
}

#[logic(open)]
pub fn ext_a_materials(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        match p_array(o, key_materials()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_material(nth(l, t), x), _ => false }
    }
}

#[logic(open)]
pub fn key_materials() -> Seq<u8> {
    pearlite! { seq![109u8, 97u8, 116u8, 101u8, 114u8, 105u8, 97u8, 108u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 9 && s[0] == 109u8 && s[1] == 97u8 && s[2] == 116u8 && s[3] == 101u8 && s[4] == 114u8 && s[5] == 105u8 && s[6] == 97u8 && s[7] == 108u8 && s[8] == 115u8 ==> seq_is(key_materials(), s))]
pub fn lemma_key_materials(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(v) => rd_a_materials(obj_of(d@, o@), v@) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_a_materials(obj_of(d@, o@), x))),
    Err(e) => e == GltfError::Invalid && forall<v: Seq<Material>> !rd_a_materials(obj_of(d@, o@), v),
})]
#[check(terminates)]
fn read_materials(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Material>, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_materials(Seq::empty()));
    match get_array(d, o, &[b'm', b'a', b't', b'e', b'r', b'i', b'a', b'l', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_materials_items(d, a, ext),
    }
}

#[logic(open)]
pub fn rd_texture(j: JsonS, x: Texture) -> bool {
    pearlite! { is_object(j) && rd_texture_o(obj_or_nil(j), x) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && (forall<t> 0 <= t && t < v@.len() ==> rd_texture(nth(list_of(d@, a@), t), v@[t]))
        && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_obj(nth(list_of(d@, a@), t), x))),
    Err(e) => e == GltfError::Invalid && exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: Texture> !rd_texture(nth(list_of(d@, a@), t), y),
})]
#[check(terminates)]
fn read_textures_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Texture>, GltfError> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<Texture> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_texture(tree(d@, a@[t]@), out@[t]))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_obj(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        proof_assert!(nth(list_of(d@, a@), i@) == tree(d@, a@[i@]@));
        proof_assert!(forall<y: Texture> rd_texture(tree(d@, a@[i@]@), y) == (is_object(tree(d@, a@[i@]@)) && rd_texture_o(obj_or_nil(tree(d@, a@[i@]@)), y)));
        match read_texture(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open)]
pub fn rd_a_textures(o: JObj, v: Seq<Texture>) -> bool {
    pearlite! {
        match p_array(o, key_textures()) {
            Err(()) => false,
            Ok(None) => v.len() == 0,
            Ok(Some(l)) => jlen(l) == v.len() && forall<t> 0 <= t && t < v.len() ==> rd_texture(nth(l, t), v[t]),
        }
    }
}

#[logic(open)]
pub fn ext_a_textures(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        match p_array(o, key_textures()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_obj(nth(l, t), x), _ => false }
    }
}

#[logic(open)]
pub fn key_textures() -> Seq<u8> {
    pearlite! { seq![116u8, 101u8, 120u8, 116u8, 117u8, 114u8, 101u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 8 && s[0] == 116u8 && s[1] == 101u8 && s[2] == 120u8 && s[3] == 116u8 && s[4] == 117u8 && s[5] == 114u8 && s[6] == 101u8 && s[7] == 115u8 ==> seq_is(key_textures(), s))]
pub fn lemma_key_textures(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(v) => rd_a_textures(obj_of(d@, o@), v@) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_a_textures(obj_of(d@, o@), x))),
    Err(e) => e == GltfError::Invalid && forall<v: Seq<Texture>> !rd_a_textures(obj_of(d@, o@), v),
})]
#[check(terminates)]
fn read_textures(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Texture>, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_textures(Seq::empty()));
    match get_array(d, o, &[b't', b'e', b'x', b't', b'u', b'r', b'e', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_textures_items(d, a, ext),
    }
}

#[logic(open)]
pub fn rd_image(j: JsonS, x: Image) -> bool {
    pearlite! { is_object(j) && rd_image_o(obj_or_nil(j), x) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && (forall<t> 0 <= t && t < v@.len() ==> rd_image(nth(list_of(d@, a@), t), v@[t]))
        && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_obj(nth(list_of(d@, a@), t), x))),
    Err(e) => e == GltfError::Invalid && exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: Image> !rd_image(nth(list_of(d@, a@), t), y),
})]
#[check(terminates)]
fn read_images_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Image>, GltfError> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<Image> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_image(tree(d@, a@[t]@), out@[t]))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_obj(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        proof_assert!(nth(list_of(d@, a@), i@) == tree(d@, a@[i@]@));
        proof_assert!(forall<y: Image> rd_image(tree(d@, a@[i@]@), y) == (is_object(tree(d@, a@[i@]@)) && rd_image_o(obj_or_nil(tree(d@, a@[i@]@)), y)));
        match read_image(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open)]
pub fn rd_a_images(o: JObj, v: Seq<Image>) -> bool {
    pearlite! {
        match p_array(o, key_images()) {
            Err(()) => false,
            Ok(None) => v.len() == 0,
            Ok(Some(l)) => jlen(l) == v.len() && forall<t> 0 <= t && t < v.len() ==> rd_image(nth(l, t), v[t]),
        }
    }
}

#[logic(open)]
pub fn ext_a_images(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        match p_array(o, key_images()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_obj(nth(l, t), x), _ => false }
    }
}

#[logic(open)]
pub fn key_images() -> Seq<u8> {
    pearlite! { seq![105u8, 109u8, 97u8, 103u8, 101u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 6 && s[0] == 105u8 && s[1] == 109u8 && s[2] == 97u8 && s[3] == 103u8 && s[4] == 101u8 && s[5] == 115u8 ==> seq_is(key_images(), s))]
pub fn lemma_key_images(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(v) => rd_a_images(obj_of(d@, o@), v@) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_a_images(obj_of(d@, o@), x))),
    Err(e) => e == GltfError::Invalid && forall<v: Seq<Image>> !rd_a_images(obj_of(d@, o@), v),
})]
#[check(terminates)]
fn read_images(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Image>, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_images(Seq::empty()));
    match get_array(d, o, &[b'i', b'm', b'a', b'g', b'e', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_images_items(d, a, ext),
    }
}

#[logic(open)]
pub fn rd_camera(j: JsonS, x: Camera) -> bool {
    pearlite! { is_object(j) && rd_camera_o(obj_or_nil(j), x) }
}

#[logic(open)]
pub fn ext_camera(j: JsonS, x: Seq<u8>) -> bool {
    pearlite! { is_object(j) && ext_camera_o(obj_or_nil(j), x) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && (forall<t> 0 <= t && t < v@.len() ==> rd_camera(nth(list_of(d@, a@), t), v@[t]))
        && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_camera(nth(list_of(d@, a@), t), x))),
    Err(e) => e == GltfError::Invalid && exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: Camera> !rd_camera(nth(list_of(d@, a@), t), y),
})]
#[check(terminates)]
fn read_cameras_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Camera>, GltfError> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<Camera> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_camera(tree(d@, a@[t]@), out@[t]))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_camera(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        proof_assert!(nth(list_of(d@, a@), i@) == tree(d@, a@[i@]@));
        proof_assert!(forall<y: Camera> rd_camera(tree(d@, a@[i@]@), y) == (is_object(tree(d@, a@[i@]@)) && rd_camera_o(obj_or_nil(tree(d@, a@[i@]@)), y)));
        match read_camera(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open)]
pub fn rd_a_cameras(o: JObj, v: Seq<Camera>) -> bool {
    pearlite! {
        match p_array(o, key_cameras()) {
            Err(()) => false,
            Ok(None) => v.len() == 0,
            Ok(Some(l)) => jlen(l) == v.len() && forall<t> 0 <= t && t < v.len() ==> rd_camera(nth(l, t), v[t]),
        }
    }
}

#[logic(open)]
pub fn ext_a_cameras(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        match p_array(o, key_cameras()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_camera(nth(l, t), x), _ => false }
    }
}

#[logic(open)]
pub fn key_cameras() -> Seq<u8> {
    pearlite! { seq![99u8, 97u8, 109u8, 101u8, 114u8, 97u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 7 && s[0] == 99u8 && s[1] == 97u8 && s[2] == 109u8 && s[3] == 101u8 && s[4] == 114u8 && s[5] == 97u8 && s[6] == 115u8 ==> seq_is(key_cameras(), s))]
pub fn lemma_key_cameras(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(v) => rd_a_cameras(obj_of(d@, o@), v@) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_a_cameras(obj_of(d@, o@), x))),
    Err(e) => e == GltfError::Invalid && forall<v: Seq<Camera>> !rd_a_cameras(obj_of(d@, o@), v),
})]
#[check(terminates)]
fn read_cameras(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Camera>, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_cameras(Seq::empty()));
    match get_array(d, o, &[b'c', b'a', b'm', b'e', b'r', b'a', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_cameras_items(d, a, ext),
    }
}

#[logic(open)]
pub fn rd_skin(j: JsonS, x: Skin) -> bool {
    pearlite! { is_object(j) && rd_skin_o(obj_or_nil(j), x) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && (forall<t> 0 <= t && t < v@.len() ==> rd_skin(nth(list_of(d@, a@), t), v@[t]))
        && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_obj(nth(list_of(d@, a@), t), x))),
    Err(e) => e == GltfError::Invalid && exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: Skin> !rd_skin(nth(list_of(d@, a@), t), y),
})]
#[check(terminates)]
fn read_skins_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Skin>, GltfError> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<Skin> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_skin(tree(d@, a@[t]@), out@[t]))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_obj(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        proof_assert!(nth(list_of(d@, a@), i@) == tree(d@, a@[i@]@));
        proof_assert!(forall<y: Skin> rd_skin(tree(d@, a@[i@]@), y) == (is_object(tree(d@, a@[i@]@)) && rd_skin_o(obj_or_nil(tree(d@, a@[i@]@)), y)));
        match read_skin(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open)]
pub fn rd_a_skins(o: JObj, v: Seq<Skin>) -> bool {
    pearlite! {
        match p_array(o, key_skins()) {
            Err(()) => false,
            Ok(None) => v.len() == 0,
            Ok(Some(l)) => jlen(l) == v.len() && forall<t> 0 <= t && t < v.len() ==> rd_skin(nth(l, t), v[t]),
        }
    }
}

#[logic(open)]
pub fn ext_a_skins(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        match p_array(o, key_skins()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_obj(nth(l, t), x), _ => false }
    }
}

#[logic(open)]
pub fn key_skins() -> Seq<u8> {
    pearlite! { seq![115u8, 107u8, 105u8, 110u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 5 && s[0] == 115u8 && s[1] == 107u8 && s[2] == 105u8 && s[3] == 110u8 && s[4] == 115u8 ==> seq_is(key_skins(), s))]
pub fn lemma_key_skins(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(v) => rd_a_skins(obj_of(d@, o@), v@) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_a_skins(obj_of(d@, o@), x))),
    Err(e) => e == GltfError::Invalid && forall<v: Seq<Skin>> !rd_a_skins(obj_of(d@, o@), v),
})]
#[check(terminates)]
fn read_skins(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Skin>, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_skins(Seq::empty()));
    match get_array(d, o, &[b's', b'k', b'i', b'n', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_skins_items(d, a, ext),
    }
}

#[logic(open)]
pub fn rd_animation(j: JsonS, x: Animation, strict: bool) -> bool {
    pearlite! { is_object(j) && rd_animation_o(obj_or_nil(j), x, strict) }
}

#[logic(open)]
pub fn ext_animation(j: JsonS, x: Seq<u8>) -> bool {
    pearlite! { is_object(j) && ext_animation_o(obj_or_nil(j), x) }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(v) => jlen(list_of(d@, a@)) == v@.len() && (forall<t> 0 <= t && t < v@.len() ==> rd_animation(nth(list_of(d@, a@), t), v@[t], true))
        && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_animation(nth(list_of(d@, a@), t), x))),
    Err(e) => (exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: Animation> !rd_animation(nth(list_of(d@, a@), t), y, true))
        && (e == GltfError::Invalid ==> exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && forall<y: Animation> !rd_animation(nth(list_of(d@, a@), t), y, false))
        && (e == GltfError::Unsupported ==> exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && unsup_animation(nth(list_of(d@, a@), t)))
        && (e == GltfError::Invalid || e == GltfError::Unsupported),
})]
#[check(terminates)]
fn read_animations_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Animation>, GltfError> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut out: Vec<Animation> = Vec::new();
    let mut i = 0;
    #[invariant(i@ <= a@.len() && out@.len() == i@)]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_animation(tree(d@, a@[t]@), out@[t], true))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_animation(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        proof_assert!(nth(list_of(d@, a@), i@) == tree(d@, a@[i@]@));
        proof_assert!(forall<y: Animation> rd_animation(tree(d@, a@[i@]@), y, true) == (is_object(tree(d@, a@[i@]@)) && rd_animation_o(obj_or_nil(tree(d@, a@[i@]@)), y, true)));
        match read_animation(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(e) => return Err(e),
        }
        i += 1;
    }
    Ok(out)
}

#[logic(open)]
pub fn rd_a_animations(o: JObj, v: Seq<Animation>, strict: bool) -> bool {
    pearlite! {
        match p_array(o, key_animations()) {
            Err(()) => false,
            Ok(None) => v.len() == 0,
            Ok(Some(l)) => jlen(l) == v.len() && forall<t> 0 <= t && t < v.len() ==> rd_animation(nth(l, t), v[t], strict),
        }
    }
}

#[logic(open)]
pub fn ext_a_animations(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        match p_array(o, key_animations()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_animation(nth(l, t), x), _ => false }
    }
}

#[logic(open)]
pub fn unsup_a_animations(o: JObj) -> bool {
    pearlite! {
        match p_array(o, key_animations()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && unsup_animation(nth(l, t)), _ => false }
    }
}

#[logic(open)]
pub fn key_animations() -> Seq<u8> {
    pearlite! { seq![97u8, 110u8, 105u8, 109u8, 97u8, 116u8, 105u8, 111u8, 110u8, 115u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 10 && s[0] == 97u8 && s[1] == 110u8 && s[2] == 105u8 && s[3] == 109u8 && s[4] == 97u8 && s[5] == 116u8 && s[6] == 105u8 && s[7] == 111u8 && s[8] == 110u8 && s[9] == 115u8 ==> seq_is(key_animations(), s))]
pub fn lemma_key_animations(s: Seq<u8>) {}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(v) => rd_a_animations(obj_of(d@, o@), v@, true) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_a_animations(obj_of(d@, o@), x))),
    Err(e) => (forall<v: Seq<Animation>> !rd_a_animations(obj_of(d@, o@), v, true))
        && (e == GltfError::Invalid ==> forall<v: Seq<Animation>> !rd_a_animations(obj_of(d@, o@), v, false))
        && (e == GltfError::Unsupported ==> unsup_a_animations(obj_of(d@, o@)))
        && (e == GltfError::Invalid || e == GltfError::Unsupported),
})]
#[check(terminates)]
fn read_animations(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<Vec<Animation>, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_animations(Seq::empty()));
    match get_array(d, o, &[b'a', b'n', b'i', b'm', b'a', b't', b'i', b'o', b'n', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_animations_items(d, a, ext),
    }
}

#[requires(nodes_wf(d@) && ids_in(d@, a@))]
#[ensures(match result {
    Ok(()) => (forall<t> 0 <= t && t < jlen(list_of(d@, a@)) ==> rd_sampler(nth(list_of(d@, a@), t))) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || exists<t> 0 <= t && t < a@.len() && ext_obj(nth(list_of(d@, a@), t), x))),
    Err(e) => e == GltfError::Invalid && exists<t> 0 <= t && t < jlen(list_of(d@, a@)) && !rd_sampler(nth(list_of(d@, a@), t)),
})]
#[check(terminates)]
fn check_sampler_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> Result<(), GltfError> {
    let _ext0 = snapshot!(ext@);
    snapshot!(lemma_list_index(d@, a@));
    let mut i = 0;
    #[invariant(i@ <= a@.len())]
    #[invariant(forall<t> 0 <= t && t < i@ ==> rd_sampler(tree(d@, a@[t]@)))]
    #[invariant(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_ext0, x) || exists<t> 0 <= t && t < i@ && ext_obj(tree(d@, a@[t]@), x)))]
    #[variant(a@.len() - i@)]
    while i < a.len() {
        match read_sampler(d, a[i], ext) {
            Ok(()) => {}
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    Ok(())
}

#[logic(open)]
pub fn rd_a_samplers(o: JObj, n: u64) -> bool {
    pearlite! {
        match p_array(o, key_samplers()) {
            Err(()) => false,
            Ok(None) => n@ == 0,
            Ok(Some(l)) => n@ == jlen(l) && forall<t> 0 <= t && t < jlen(l) ==> rd_sampler(nth(l, t)),
        }
    }
}

#[logic(open)]
pub fn ext_a_samplers(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        match p_array(o, key_samplers()) { Ok(Some(l)) => exists<t> 0 <= t && t < jlen(l) && ext_obj(nth(l, t), x), _ => false }
    }
}

#[requires(nodes_wf(d@) && ms_in(d@, o@))]
#[ensures(match result {
    Ok(n) => rd_a_samplers(obj_of(d@, o@), n) && (forall<x: Seq<u8>> in_strs((^ext)@, x) == (in_strs((*ext)@, x) || ext_a_samplers(obj_of(d@, o@), x))),
    Err(e) => e == GltfError::Invalid && forall<n: u64> !rd_a_samplers(obj_of(d@, o@), n),
})]
#[check(terminates)]
fn read_samplers(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> Result<u64, GltfError> {
    snapshot!(lemma_list_index(d@, Seq::empty()));
    snapshot!(lemma_key_samplers(Seq::empty()));
    match get_array(d, o, &[b's', b'a', b'm', b'p', b'l', b'e', b'r', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(0),
        Ok(Some(a)) => match check_sampler_items(d, a, ext) {
            Err(e) => Err(e),
            Ok(()) => Ok(a.len() as u64),
        },
    }
}

// MUST-002, MUST-008, MUST-009: asset と asset.version が必要
#[logic(open)]
pub fn rd_asset(o: JObj, major: u64, minor: u64, minv: Option<(u64, u64)>) -> bool {
    pearlite! {
        match p_object(o, key_asset()) {
            Ok(Some(a)) => ext_ok(a)
                && p_string(a, key_copyright()) != Err(())
                && p_string(a, key_generator()) != Err(())
                && (match p_string(a, key_version()) { Ok(Some(v)) => version_is(v, major@, minor@), _ => false })
                && match p_string(a, key_min_version()) {
                    Err(()) => false,
                    Ok(None) => minv == None,
                    Ok(Some(v)) => match minv { Some((x, y)) => version_is(v, x@, y@), None => false },
                },
            _ => false,
        }
    }
}

// ルートの asset・extensionsUsed・extensionsRequired・scene
#[logic(open)]
pub fn rd_head(o: JObj, major: u64, minor: u64, minv: Option<(u64, u64)>, eu: Seq<Vec<u8>>, er: Seq<Vec<u8>>, scene: Option<u64>) -> bool {
    pearlite! {
        ext_ok(o) && rd_asset(o, major, minor, minv)
            && f_string_array(o, key_extensions_used(), eu)
            && f_string_array(o, key_extensions_required(), er)
            && f_uint_opt(o, key_scene(), scene)
    }
}

// read_spec(j, is_glb, bin_len) = Ok(g)（extensions_present 以外の欄）
#[logic(open)]
pub fn rd_root(o: JObj, is_glb: bool, bin: Option<Int>, g: Gltf, strict: bool) -> bool {
    pearlite! {
        rd_head(o, g.version_major, g.version_minor, g.min_version, g.extensions_used@, g.extensions_required@, g.scene)
            && rd_a_scenes(o, g.scenes@)
            && rd_a_nodes(o, g.nodes@)
            && rd_a_meshes(o, g.meshes@)
            && rd_a_accessors(o, g.accessors@, strict)
            && rd_a_buffer_views(o, g.buffer_views@)
            && rd_a_buffers(o, g.buffers@)
            && rd_a_materials(o, g.materials@)
            && rd_a_textures(o, g.textures@)
            && rd_a_images(o, g.images@)
            && rd_a_samplers(o, g.samplers_len)
            && rd_a_cameras(o, g.cameras@)
            && rd_a_skins(o, g.skins@)
            && rd_a_animations(o, g.animations@, strict)
            && g.is_glb == is_glb && opt_int(g.glb_bin_len) == bin
    }
}

#[logic(open)]
pub fn ext_asset(o: JObj, x: Seq<u8>) -> bool {
    pearlite! { match p_object(o, key_asset()) { Ok(Some(a)) => ext_here(a, x), _ => false } }
}

// extensions_present: 読んだ glTFProperty の extensions のメンバーのキー
#[logic(open)]
pub fn ext_root(o: JObj, x: Seq<u8>) -> bool {
    pearlite! {
        ext_here(o, x)
            || ext_asset(o, x)
            || ext_a_scenes(o, x) || ext_a_nodes(o, x) || ext_a_meshes(o, x) || ext_a_accessors(o, x)
            || ext_a_buffer_views(o, x) || ext_a_buffers(o, x) || ext_a_materials(o, x) || ext_a_textures(o, x)
            || ext_a_images(o, x) || ext_a_samplers(o, x) || ext_a_cameras(o, x) || ext_a_skins(o, x)
            || ext_a_animations(o, x)
    }
}

// rd_root の各部分（read_gltf の失敗の場合の証明に使う）
#[logic(opaque)]
#[ensures(forall<g: Gltf, st: bool> rd_root(o, is_glb, bin, g, st) ==>
    ext_ok(o) && rd_asset(o, g.version_major, g.version_minor, g.min_version)
    && (match p_array(o, key_extensions_used()) { Err(()) => false, Ok(None) => g.extensions_used@.len() == 0, Ok(Some(l)) => strings_is(l, g.extensions_used@) })
    && (match p_array(o, key_extensions_required()) { Err(()) => false, Ok(None) => g.extensions_required@.len() == 0, Ok(Some(l)) => strings_is(l, g.extensions_required@) })
    && p_uint(o, key_scene()) == Ok(opt_int(g.scene))
    && rd_a_scenes(o, g.scenes@) && rd_a_nodes(o, g.nodes@) && rd_a_meshes(o, g.meshes@) && rd_a_accessors(o, g.accessors@, st)
    && rd_a_buffer_views(o, g.buffer_views@) && rd_a_buffers(o, g.buffers@) && rd_a_materials(o, g.materials@) && rd_a_textures(o, g.textures@)
    && rd_a_images(o, g.images@) && rd_a_samplers(o, g.samplers_len) && rd_a_cameras(o, g.cameras@) && rd_a_skins(o, g.skins@)
    && rd_a_animations(o, g.animations@, st))]
pub fn lemma_root_proj(o: JObj, is_glb: bool, bin: Option<Int>) {}

#[logic(opaque)]
#[ensures(forall<a: JObj, major: u64, minor: u64, minv: Option<(u64, u64)>> rd_asset(o, major, minor, minv) && p_object(o, key_asset()) == Ok(Some(a)) ==>
    ext_ok(a) && p_string(a, key_copyright()) != Err(()) && p_string(a, key_generator()) != Err(())
    && (match p_string(a, key_version()) { Ok(Some(s)) => version_is(s, major@, minor@), _ => false })
    && (match p_string(a, key_min_version()) { Err(()) => false, Ok(None) => minv == None, Ok(Some(s)) => match minv { Some((x, y)) => version_is(s, x@, y@), None => false } }))]
pub fn lemma_asset_proj(o: JObj) {}

#[logic(open)]
pub fn key_asset() -> Seq<u8> {
    pearlite! { seq![97u8, 115u8, 115u8, 101u8, 116u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 5 && s[0] == 97u8 && s[1] == 115u8 && s[2] == 115u8 && s[3] == 101u8 && s[4] == 116u8 ==> seq_is(key_asset(), s))]
pub fn lemma_key_asset(s: Seq<u8>) {}

#[logic(open)]
pub fn key_copyright() -> Seq<u8> {
    pearlite! { seq![99u8, 111u8, 112u8, 121u8, 114u8, 105u8, 103u8, 104u8, 116u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 9 && s[0] == 99u8 && s[1] == 111u8 && s[2] == 112u8 && s[3] == 121u8 && s[4] == 114u8 && s[5] == 105u8 && s[6] == 103u8 && s[7] == 104u8 && s[8] == 116u8 ==> seq_is(key_copyright(), s))]
pub fn lemma_key_copyright(s: Seq<u8>) {}

#[logic(open)]
pub fn key_extensions_required() -> Seq<u8> {
    pearlite! { seq![101u8, 120u8, 116u8, 101u8, 110u8, 115u8, 105u8, 111u8, 110u8, 115u8, 82u8, 101u8, 113u8, 117u8, 105u8, 114u8, 101u8, 100u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 18 && s[0] == 101u8 && s[1] == 120u8 && s[2] == 116u8 && s[3] == 101u8 && s[4] == 110u8 && s[5] == 115u8 && s[6] == 105u8 && s[7] == 111u8 && s[8] == 110u8 && s[9] == 115u8 && s[10] == 82u8 && s[11] == 101u8 && s[12] == 113u8 && s[13] == 117u8 && s[14] == 105u8 && s[15] == 114u8 && s[16] == 101u8 && s[17] == 100u8 ==> seq_is(key_extensions_required(), s))]
pub fn lemma_key_extensions_required(s: Seq<u8>) {}

#[logic(open)]
pub fn key_extensions_used() -> Seq<u8> {
    pearlite! { seq![101u8, 120u8, 116u8, 101u8, 110u8, 115u8, 105u8, 111u8, 110u8, 115u8, 85u8, 115u8, 101u8, 100u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 14 && s[0] == 101u8 && s[1] == 120u8 && s[2] == 116u8 && s[3] == 101u8 && s[4] == 110u8 && s[5] == 115u8 && s[6] == 105u8 && s[7] == 111u8 && s[8] == 110u8 && s[9] == 115u8 && s[10] == 85u8 && s[11] == 115u8 && s[12] == 101u8 && s[13] == 100u8 ==> seq_is(key_extensions_used(), s))]
pub fn lemma_key_extensions_used(s: Seq<u8>) {}

#[logic(open)]
pub fn key_generator() -> Seq<u8> {
    pearlite! { seq![103u8, 101u8, 110u8, 101u8, 114u8, 97u8, 116u8, 111u8, 114u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 9 && s[0] == 103u8 && s[1] == 101u8 && s[2] == 110u8 && s[3] == 101u8 && s[4] == 114u8 && s[5] == 97u8 && s[6] == 116u8 && s[7] == 111u8 && s[8] == 114u8 ==> seq_is(key_generator(), s))]
pub fn lemma_key_generator(s: Seq<u8>) {}

#[logic(open)]
pub fn key_min_version() -> Seq<u8> {
    pearlite! { seq![109u8, 105u8, 110u8, 86u8, 101u8, 114u8, 115u8, 105u8, 111u8, 110u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 10 && s[0] == 109u8 && s[1] == 105u8 && s[2] == 110u8 && s[3] == 86u8 && s[4] == 101u8 && s[5] == 114u8 && s[6] == 115u8 && s[7] == 105u8 && s[8] == 111u8 && s[9] == 110u8 ==> seq_is(key_min_version(), s))]
pub fn lemma_key_min_version(s: Seq<u8>) {}

#[logic(open)]
pub fn key_scene() -> Seq<u8> {
    pearlite! { seq![115u8, 99u8, 101u8, 110u8, 101u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 5 && s[0] == 115u8 && s[1] == 99u8 && s[2] == 101u8 && s[3] == 110u8 && s[4] == 101u8 ==> seq_is(key_scene(), s))]
pub fn lemma_key_scene(s: Seq<u8>) {}

#[logic(open)]
pub fn key_version() -> Seq<u8> {
    pearlite! { seq![118u8, 101u8, 114u8, 115u8, 105u8, 111u8, 110u8] }
}

#[logic(opaque)]
#[ensures(s.len() == 7 && s[0] == 118u8 && s[1] == 101u8 && s[2] == 114u8 && s[3] == 115u8 && s[4] == 105u8 && s[5] == 111u8 && s[6] == 110u8 ==> seq_is(key_version(), s))]
pub fn lemma_key_version(s: Seq<u8>) {}

// MUST-002, MUST-008, MUST-009: asset と asset.version が必要
#[requires(doc_wf(*doc))]
#[ensures(match result {
    Ok(g) => is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, true)
        && forall<x: Seq<u8>> in_strs(g.extensions_present@, x) == ext_root(obj_or_nil(tree(doc.nodes@, doc.root@)), x),
    Err(e) => (forall<g: Gltf> !(is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, true)))
        && (e == GltfError::Invalid ==> forall<g: Gltf> !(is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, false)))
        && (e == GltfError::Unsupported ==> is_object(tree(doc.nodes@, doc.root@)) && (unsup_a_accessors(obj_or_nil(tree(doc.nodes@, doc.root@))) || unsup_a_animations(obj_or_nil(tree(doc.nodes@, doc.root@)))))
        && (e == GltfError::Invalid || e == GltfError::Unsupported),
})]
#[check(terminates)]
pub fn read_gltf(doc: &JsonDoc, is_glb: bool, glb_bin_len: Option<u64>) -> Result<Gltf, GltfError> {
    snapshot!(lemma_list_index(doc.nodes@, Seq::empty()));
    snapshot!(lemma_key_asset(Seq::empty()));
    snapshot!(lemma_key_copyright(Seq::empty()));
    snapshot!(lemma_key_generator(Seq::empty()));
    snapshot!(lemma_key_version(Seq::empty()));
    snapshot!(lemma_key_min_version(Seq::empty()));
    snapshot!(lemma_key_extensions_used(Seq::empty()));
    snapshot!(lemma_key_extensions_required(Seq::empty()));
    snapshot!(lemma_key_scene(Seq::empty()));
    snapshot!(lemma_root_proj(JObj::Nil, is_glb, opt_int(glb_bin_len)));
    snapshot!(lemma_asset_proj(JObj::Nil));
    let mut extensions_present: Vec<Vec<u8>> = Vec::new();
    let ext = &mut extensions_present;
    let d = &doc.nodes;
    let _e0 = snapshot!(ext@);
    let o = match as_object(d, doc.root) { Ok(o) => o, Err(()) => return Err(GltfError::Invalid) };
    proof_assert!(obj_or_nil(tree(doc.nodes@, doc.root@)) == obj_of(d@, o@));
    match check_extensions(d, o, ext) { Err(()) => return Err(GltfError::Invalid), Ok(()) => {} }
        proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e0, x) || ext_here(obj_of(d@, o@), x)));
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> ext_ok(obj_of(d@, o@)));
    let asset = match get_object(d, o, &[b'a', b's', b's', b'e', b't']) { Ok(Some(a)) => a, _ => return Err(GltfError::Invalid) };
    proof_assert!(p_object(obj_of(d@, o@), key_asset()) == Ok(Some(obj_of(d@, asset@))));
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> ext_ok(obj_of(d@, asset@)) && p_string(obj_of(d@, asset@), key_copyright()) != Err(()) && p_string(obj_of(d@, asset@), key_generator()) != Err(()) && (match p_string(obj_of(d@, asset@), key_version()) { Ok(Some(v)) => version_is(v, g.version_major@, g.version_minor@), _ => false }) && (match p_string(obj_of(d@, asset@), key_min_version()) { Err(()) => false, Ok(None) => g.min_version == None, Ok(Some(v)) => match g.min_version { Some((x, y)) => version_is(v, x@, y@), None => false } }));
    match check_extensions(d, asset, ext) { Err(()) => return Err(GltfError::Invalid), Ok(()) => {} }
        proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e0, x) || ext_here(obj_of(d@, o@), x) || ext_asset(obj_of(d@, o@), x)));
        proof_assert!(ext_ok(obj_of(d@, asset@)));
    match get_string(d, asset, &[b'c', b'o', b'p', b'y', b'r', b'i', b'g', b'h', b't']) { Err(()) => return Err(GltfError::Invalid), Ok(_) => {} }
        proof_assert!(p_string(obj_of(d@, asset@), key_copyright()) != Err(()));
    match get_string(d, asset, &[b'g', b'e', b'n', b'e', b'r', b'a', b't', b'o', b'r']) { Err(()) => return Err(GltfError::Invalid), Ok(_) => {} }
        proof_assert!(p_string(obj_of(d@, asset@), key_generator()) != Err(()));
    let (version_major, version_minor) = match get_string(d, asset, &[b'v', b'e', b'r', b's', b'i', b'o', b'n']) {
        Ok(Some(v)) => match parse_version(&v) { Some(p) => p, None => return Err(GltfError::Invalid) },
        _ => return Err(GltfError::Invalid),
    };
    proof_assert!(match p_string(obj_of(d@, asset@), key_version()) { Ok(Some(s)) => version_is(s, version_major@, version_minor@), _ => false });
    let min_version = match get_string(d, asset, &[b'm', b'i', b'n', b'V', b'e', b'r', b's', b'i', b'o', b'n']) {
        Err(()) => return Err(GltfError::Invalid),
        Ok(None) => None,
        Ok(Some(v)) => match parse_version(&v) { Some(p) => Some(p), None => return Err(GltfError::Invalid) },
    };
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> match p_array(obj_of(d@, o@), key_extensions_used()) { Err(()) => false, Ok(None) => g.extensions_used@.len() == 0, Ok(Some(l)) => strings_is(l, g.extensions_used@) });
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> match p_array(obj_of(d@, o@), key_extensions_required()) { Err(()) => false, Ok(None) => g.extensions_required@.len() == 0, Ok(Some(l)) => strings_is(l, g.extensions_required@) });
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> p_uint(obj_of(d@, o@), key_scene()) == Ok(opt_int(g.scene)));
    proof_assert!(match p_string(obj_of(d@, asset@), key_min_version()) { Err(()) => false, Ok(None) => min_version == None, Ok(Some(s)) => match min_version { Some((x, y)) => version_is(s, x@, y@), None => false } });
    let extensions_used = match read_string_array(d, o, &[b'e', b'x', b't', b'e', b'n', b's', b'i', b'o', b'n', b's', b'U', b's', b'e', b'd']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    proof_assert!(match p_array(obj_of(d@, o@), key_extensions_used()) { Err(()) => false, Ok(None) => extensions_used@.len() == 0, Ok(Some(l)) => strings_is(l, extensions_used@) });
    let extensions_required = match read_string_array(d, o, &[b'e', b'x', b't', b'e', b'n', b's', b'i', b'o', b'n', b's', b'R', b'e', b'q', b'u', b'i', b'r', b'e', b'd']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    proof_assert!(match p_array(obj_of(d@, o@), key_extensions_required()) { Err(()) => false, Ok(None) => extensions_required@.len() == 0, Ok(Some(l)) => strings_is(l, extensions_required@) });
    let scene = match get_uint(d, o, &[b's', b'c', b'e', b'n', b'e']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    proof_assert!(p_uint(obj_of(d@, o@), key_scene()) == Ok(opt_int(scene)));
    proof_assert!(rd_asset(obj_of(d@, o@), version_major, version_minor, min_version));
    proof_assert!(rd_head(obj_of(d@, o@), version_major, version_minor, min_version, extensions_used@, extensions_required@, scene));

    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> rd_a_scenes(obj_of(d@, o@), g.scenes@));
    let scenes = match read_scenes(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    proof_assert!(rd_a_scenes(obj_of(d@, o@), scenes@));
    proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e0, x) || ext_here(obj_of(d@, o@), x) || ext_asset(obj_of(d@, o@), x) || ext_a_scenes(obj_of(d@, o@), x)));
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> rd_a_nodes(obj_of(d@, o@), g.nodes@));
    let nodes = match read_nodes(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    proof_assert!(rd_a_nodes(obj_of(d@, o@), nodes@));
    proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e0, x) || ext_here(obj_of(d@, o@), x) || ext_asset(obj_of(d@, o@), x) || ext_a_scenes(obj_of(d@, o@), x) || ext_a_nodes(obj_of(d@, o@), x)));
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> rd_a_meshes(obj_of(d@, o@), g.meshes@));
    let meshes = match read_meshes(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    proof_assert!(rd_a_meshes(obj_of(d@, o@), meshes@));
    proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e0, x) || ext_here(obj_of(d@, o@), x) || ext_asset(obj_of(d@, o@), x) || ext_a_scenes(obj_of(d@, o@), x) || ext_a_nodes(obj_of(d@, o@), x) || ext_a_meshes(obj_of(d@, o@), x)));
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> rd_a_accessors(obj_of(d@, o@), g.accessors@, st));
    let accessors = match read_accessors(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    proof_assert!(rd_a_accessors(obj_of(d@, o@), accessors@, true));
    proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e0, x) || ext_here(obj_of(d@, o@), x) || ext_asset(obj_of(d@, o@), x) || ext_a_scenes(obj_of(d@, o@), x) || ext_a_nodes(obj_of(d@, o@), x) || ext_a_meshes(obj_of(d@, o@), x) || ext_a_accessors(obj_of(d@, o@), x)));
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> rd_a_buffer_views(obj_of(d@, o@), g.buffer_views@));
    let buffer_views = match read_buffer_views(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    proof_assert!(rd_a_buffer_views(obj_of(d@, o@), buffer_views@));
    proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e0, x) || ext_here(obj_of(d@, o@), x) || ext_asset(obj_of(d@, o@), x) || ext_a_scenes(obj_of(d@, o@), x) || ext_a_nodes(obj_of(d@, o@), x) || ext_a_meshes(obj_of(d@, o@), x) || ext_a_accessors(obj_of(d@, o@), x) || ext_a_buffer_views(obj_of(d@, o@), x)));
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> rd_a_buffers(obj_of(d@, o@), g.buffers@));
    let buffers = match read_buffers(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    proof_assert!(rd_a_buffers(obj_of(d@, o@), buffers@));
    proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e0, x) || ext_here(obj_of(d@, o@), x) || ext_asset(obj_of(d@, o@), x) || ext_a_scenes(obj_of(d@, o@), x) || ext_a_nodes(obj_of(d@, o@), x) || ext_a_meshes(obj_of(d@, o@), x) || ext_a_accessors(obj_of(d@, o@), x) || ext_a_buffer_views(obj_of(d@, o@), x) || ext_a_buffers(obj_of(d@, o@), x)));
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> rd_a_materials(obj_of(d@, o@), g.materials@));
    let materials = match read_materials(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    proof_assert!(rd_a_materials(obj_of(d@, o@), materials@));
    proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e0, x) || ext_here(obj_of(d@, o@), x) || ext_asset(obj_of(d@, o@), x) || ext_a_scenes(obj_of(d@, o@), x) || ext_a_nodes(obj_of(d@, o@), x) || ext_a_meshes(obj_of(d@, o@), x) || ext_a_accessors(obj_of(d@, o@), x) || ext_a_buffer_views(obj_of(d@, o@), x) || ext_a_buffers(obj_of(d@, o@), x) || ext_a_materials(obj_of(d@, o@), x)));
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> rd_a_textures(obj_of(d@, o@), g.textures@));
    let textures = match read_textures(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    proof_assert!(rd_a_textures(obj_of(d@, o@), textures@));
    proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e0, x) || ext_here(obj_of(d@, o@), x) || ext_asset(obj_of(d@, o@), x) || ext_a_scenes(obj_of(d@, o@), x) || ext_a_nodes(obj_of(d@, o@), x) || ext_a_meshes(obj_of(d@, o@), x) || ext_a_accessors(obj_of(d@, o@), x) || ext_a_buffer_views(obj_of(d@, o@), x) || ext_a_buffers(obj_of(d@, o@), x) || ext_a_materials(obj_of(d@, o@), x) || ext_a_textures(obj_of(d@, o@), x)));
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> rd_a_images(obj_of(d@, o@), g.images@));
    let images = match read_images(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    proof_assert!(rd_a_images(obj_of(d@, o@), images@));
    proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e0, x) || ext_here(obj_of(d@, o@), x) || ext_asset(obj_of(d@, o@), x) || ext_a_scenes(obj_of(d@, o@), x) || ext_a_nodes(obj_of(d@, o@), x) || ext_a_meshes(obj_of(d@, o@), x) || ext_a_accessors(obj_of(d@, o@), x) || ext_a_buffer_views(obj_of(d@, o@), x) || ext_a_buffers(obj_of(d@, o@), x) || ext_a_materials(obj_of(d@, o@), x) || ext_a_textures(obj_of(d@, o@), x) || ext_a_images(obj_of(d@, o@), x)));
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> rd_a_samplers(obj_of(d@, o@), g.samplers_len));
    let samplers_len = match read_samplers(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    proof_assert!(rd_a_samplers(obj_of(d@, o@), samplers_len));
    proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e0, x) || ext_here(obj_of(d@, o@), x) || ext_asset(obj_of(d@, o@), x) || ext_a_scenes(obj_of(d@, o@), x) || ext_a_nodes(obj_of(d@, o@), x) || ext_a_meshes(obj_of(d@, o@), x) || ext_a_accessors(obj_of(d@, o@), x) || ext_a_buffer_views(obj_of(d@, o@), x) || ext_a_buffers(obj_of(d@, o@), x) || ext_a_materials(obj_of(d@, o@), x) || ext_a_textures(obj_of(d@, o@), x) || ext_a_images(obj_of(d@, o@), x) || ext_a_samplers(obj_of(d@, o@), x)));
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> rd_a_cameras(obj_of(d@, o@), g.cameras@));
    let cameras = match read_cameras(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    proof_assert!(rd_a_cameras(obj_of(d@, o@), cameras@));
    proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e0, x) || ext_here(obj_of(d@, o@), x) || ext_asset(obj_of(d@, o@), x) || ext_a_scenes(obj_of(d@, o@), x) || ext_a_nodes(obj_of(d@, o@), x) || ext_a_meshes(obj_of(d@, o@), x) || ext_a_accessors(obj_of(d@, o@), x) || ext_a_buffer_views(obj_of(d@, o@), x) || ext_a_buffers(obj_of(d@, o@), x) || ext_a_materials(obj_of(d@, o@), x) || ext_a_textures(obj_of(d@, o@), x) || ext_a_images(obj_of(d@, o@), x) || ext_a_samplers(obj_of(d@, o@), x) || ext_a_cameras(obj_of(d@, o@), x)));
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> rd_a_skins(obj_of(d@, o@), g.skins@));
    let skins = match read_skins(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    proof_assert!(rd_a_skins(obj_of(d@, o@), skins@));
    proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e0, x) || ext_here(obj_of(d@, o@), x) || ext_asset(obj_of(d@, o@), x) || ext_a_scenes(obj_of(d@, o@), x) || ext_a_nodes(obj_of(d@, o@), x) || ext_a_meshes(obj_of(d@, o@), x) || ext_a_accessors(obj_of(d@, o@), x) || ext_a_buffer_views(obj_of(d@, o@), x) || ext_a_buffers(obj_of(d@, o@), x) || ext_a_materials(obj_of(d@, o@), x) || ext_a_textures(obj_of(d@, o@), x) || ext_a_images(obj_of(d@, o@), x) || ext_a_samplers(obj_of(d@, o@), x) || ext_a_cameras(obj_of(d@, o@), x) || ext_a_skins(obj_of(d@, o@), x)));
    proof_assert!(forall<g: Gltf, st: bool> is_object(tree(doc.nodes@, doc.root@)) && rd_root(obj_or_nil(tree(doc.nodes@, doc.root@)), is_glb, opt_int(glb_bin_len), g, st) ==> rd_a_animations(obj_of(d@, o@), g.animations@, st));
    let animations = match read_animations(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    proof_assert!(rd_a_animations(obj_of(d@, o@), animations@, true));
    proof_assert!(forall<x: Seq<u8>> in_strs(ext@, x) == (in_strs(*_e0, x) || ext_here(obj_of(d@, o@), x) || ext_asset(obj_of(d@, o@), x) || ext_a_scenes(obj_of(d@, o@), x) || ext_a_nodes(obj_of(d@, o@), x) || ext_a_meshes(obj_of(d@, o@), x) || ext_a_accessors(obj_of(d@, o@), x) || ext_a_buffer_views(obj_of(d@, o@), x) || ext_a_buffers(obj_of(d@, o@), x) || ext_a_materials(obj_of(d@, o@), x) || ext_a_textures(obj_of(d@, o@), x) || ext_a_images(obj_of(d@, o@), x) || ext_a_samplers(obj_of(d@, o@), x) || ext_a_cameras(obj_of(d@, o@), x) || ext_a_skins(obj_of(d@, o@), x) || ext_a_animations(obj_of(d@, o@), x)));
    Ok(Gltf {
        version_major, version_minor, min_version, extensions_used, extensions_required, scene, scenes, nodes, meshes,
        accessors, buffer_views, buffers, materials, textures, images, samplers_len, cameras, skins, animations, extensions_present, is_glb, glb_bin_len,
    })
}

// R1・R2: read_gltf(j, is_glb, bin) の結果
#[logic(open)]
pub fn read_res(j: JsonS, is_glb: bool, bin: Option<Int>, r: Result<Gltf, GltfError>) -> bool {
    pearlite! {
        match r {
            Ok(g) => rd_gltf(j, is_glb, bin, g, true) && forall<x: Seq<u8>> in_strs(g.extensions_present@, x) == ext_gltf(j, x),
            Err(e) => (forall<g: Gltf> !rd_gltf(j, is_glb, bin, g, true))
                && (e == GltfError::Invalid ==> forall<g: Gltf> !rd_gltf(j, is_glb, bin, g, false))
                && (e == GltfError::Unsupported ==> unsup_gltf(j))
                && (e == GltfError::Invalid || e == GltfError::Unsupported),
        }
    }
}

#[logic(open)]
pub fn rd_gltf(j: JsonS, is_glb: bool, bin: Option<Int>, g: Gltf, strict: bool) -> bool {
    pearlite! { is_object(j) && rd_root(obj_or_nil(j), is_glb, bin, g, strict) }
}

#[logic(open)]
pub fn ext_gltf(j: JsonS, x: Seq<u8>) -> bool {
    pearlite! { is_object(j) && ext_root(obj_or_nil(j), x) }
}

// j は (U) の場合を含む
#[logic(open)]
pub fn unsup_gltf(j: JsonS) -> bool {
    pearlite! { is_object(j) && (unsup_a_accessors(obj_or_nil(j)) || unsup_a_animations(obj_or_nil(j))) }
}
