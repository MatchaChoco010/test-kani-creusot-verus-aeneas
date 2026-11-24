pub mod access;
pub mod objects;

use crate::json::*;
use crate::model::*;
use crate::read::access::*;
use crate::read::objects::*;
use vstd::prelude::*;

verus! {

pub open spec fn strings_s(a: Seq<JsonS>) -> Option<Seq<Seq<u8>>> {
    if forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]) is String {
        Some(Seq::new(a.len(), |i: int| a[i]->String_0))
    } else {
        None
    }
}

fn strings_of(d: &Vec<JsonNode>, a: &Vec<usize>) -> (r: Result<Vec<Vec<u8>>, ()>)
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => strings_s(trees(d@, a@)) == Some(strings_view(v@)),
            Err(_) => strings_s(trees(d@, a@)) is None,
        },
{
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            out@.len() == i,
            children_lt(d@) && arr_in(d@, a@) ==> forall|k: int| 0 <= k < i ==> (#[trigger] trees(d@, a@)[k]) is String && trees(d@, a@)[k]->String_0 == strings_view(out@)[k],
        decreases a.len() - i,
    {
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_trees_index(d@, a@, i as int);
            }
        }
        let ghost ob = out@;
        match node_at(d, a[i]) {
            Some(JsonNode::String(s)) => out.push(copy_key(s)),
            _ => return Err(()),
        }
        proof {
            assert forall|k: int| 0 <= k < i implies strings_view(out@)[k] == strings_view(ob)[k] by {}
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            assert(Seq::new(trees(d@, a@).len(), |k: int| trees(d@, a@)[k]->String_0) =~= strings_view(out@));
        }
    }
    Ok(out)
}

pub open spec fn string_array_s(o: Ms, k: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    match get_array_s(o, k) {
        None => None,
        Some(None) => Some(Seq::empty()),
        Some(Some(a)) => strings_s(a),
    }
}

fn read_string_array(d: &Vec<JsonNode>, o: &Vec<Member>, key: &[u8]) -> (r: Result<Vec<Vec<u8>>, ()>)
    ensures
        ctx(d@, o@) ==> match r {
            Ok(v) => string_array_s(mt(d@, o@), key@) == Some(strings_view(v@)),
            Err(_) => string_array_s(mt(d@, o@), key@) is None,
        },
{
    proof {
        assert(strings_view(Seq::<Vec<u8>>::empty()) =~= Seq::<Seq<u8>>::empty());
    }
    match get_array(d, o, key) {
        Err(()) => Err(()),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => strings_of(d, a),
    }
}

pub open spec fn scene_f() -> spec_fn(JsonS) -> Option<(SceneS, Ext)> {
    |v: JsonS| scene_s(v)
}

fn read_scenes_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Scene>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => got(items_s(trees(d@, a@), scene_f()), scenes_view(v@), old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && items_s(trees(d@, a@), scene_f()) is None,
        },
{
    let mut out: Vec<Scene> = Vec::new();
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), scene_f(), e0);
        assert(scenes_view(out@) =~= Seq::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), scene_f(), scenes_view(out@), i as int, e0, ext@),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        let ghost ob = scenes_view(out@);
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), scene_f(), i as int);
            }
        }
        match read_scene(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_step(trees(d@, a@), scene_f(), ob, scenes_view(out@), i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), scene_f(), scenes_view(out@), e0, ext@);
        }
    }
    Ok(out)
}

// 省略時は空
pub open spec fn list_s<T>(o: Ms, k: Seq<u8>, f: spec_fn(JsonS) -> Option<(T, Ext)>) -> Option<(Seq<T>, Ext)> {
    match get_array_s(o, k) {
        None => None,
        Some(None) => Some((Seq::empty(), ISet::empty())),
        Some(Some(a)) => items_s(a, f),
    }
}

fn read_scenes(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Scene>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(v) => got(list_s(mt(d@, o@), seq![b's', b'c', b'e', b'n', b'e', b's'], scene_f()), scenes_view(v@), old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && list_s(mt(d@, o@), seq![b's', b'c', b'e', b'n', b'e', b's'], scene_f()) is None,
        },
{
    proof {
        lemma_ext_refl(ext@);
        assert(scenes_view(Seq::empty()) =~= Seq::empty());
    }
    match get_array(d, o, &[b's', b'c', b'e', b'n', b'e', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_scenes_items(d, a, ext),
    }
}

pub open spec fn node_f() -> spec_fn(JsonS) -> Option<(NodeS, Ext)> {
    |v: JsonS| node_s(v)
}

fn read_nodes_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Node>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => got(items_s(trees(d@, a@), node_f()), nodes_view(v@), old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && items_s(trees(d@, a@), node_f()) is None,
        },
{
    let mut out: Vec<Node> = Vec::new();
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), node_f(), e0);
        assert(nodes_view(out@) =~= Seq::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), node_f(), nodes_view(out@), i as int, e0, ext@),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        let ghost ob = nodes_view(out@);
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), node_f(), i as int);
            }
        }
        match read_node(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_step(trees(d@, a@), node_f(), ob, nodes_view(out@), i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), node_f(), nodes_view(out@), e0, ext@);
        }
    }
    Ok(out)
}

fn read_nodes(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Node>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(v) => got(list_s(mt(d@, o@), seq![b'n', b'o', b'd', b'e', b's'], node_f()), nodes_view(v@), old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && list_s(mt(d@, o@), seq![b'n', b'o', b'd', b'e', b's'], node_f()) is None,
        },
{
    proof {
        lemma_ext_refl(ext@);
        assert(nodes_view(Seq::empty()) =~= Seq::empty());
    }
    match get_array(d, o, &[b'n', b'o', b'd', b'e', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_nodes_items(d, a, ext),
    }
}

pub open spec fn mesh_f() -> spec_fn(JsonS) -> Option<(MeshS, Ext)> {
    |v: JsonS| mesh_s(v)
}

fn read_meshes_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Mesh>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => got(items_s(trees(d@, a@), mesh_f()), meshes_view(v@), old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && items_s(trees(d@, a@), mesh_f()) is None,
        },
{
    let mut out: Vec<Mesh> = Vec::new();
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), mesh_f(), e0);
        assert(meshes_view(out@) =~= Seq::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), mesh_f(), meshes_view(out@), i as int, e0, ext@),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        let ghost ob = meshes_view(out@);
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), mesh_f(), i as int);
            }
        }
        match read_mesh(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_step(trees(d@, a@), mesh_f(), ob, meshes_view(out@), i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), mesh_f(), meshes_view(out@), e0, ext@);
        }
    }
    Ok(out)
}

fn read_meshes(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Mesh>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(v) => got(list_s(mt(d@, o@), seq![b'm', b'e', b's', b'h', b'e', b's'], mesh_f()), meshes_view(v@), old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && list_s(mt(d@, o@), seq![b'm', b'e', b's', b'h', b'e', b's'], mesh_f()) is None,
        },
{
    proof {
        lemma_ext_refl(ext@);
        assert(meshes_view(Seq::empty()) =~= Seq::empty());
    }
    match get_array(d, o, &[b'm', b'e', b's', b'h', b'e', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_meshes_items(d, a, ext),
    }
}

pub open spec fn accessor_f(strict: bool) -> spec_fn(JsonS) -> Option<(Accessor, Ext)> {
    |v: JsonS| accessor_s(v, strict)
}

fn read_accessors_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Accessor>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => got(items_s(trees(d@, a@), accessor_f(true)), v@, old(ext)@, final(ext)@) && items_s(trees(d@, a@), accessor_f(false))
                == items_s(trees(d@, a@), accessor_f(true)),
            Err(GltfError::Invalid) => items_s(trees(d@, a@), accessor_f(false)) is None && items_s(trees(d@, a@), accessor_f(true)) is None,
            Err(GltfError::Unsupported) => (exists|k: int| 0 <= k < a.len() && u_accessor(#[trigger] trees(d@, a@)[k])) && items_s(
                trees(d@, a@),
                accessor_f(true),
            ) is None,
            Err(_) => false,
        },
{
    let mut out: Vec<Accessor> = Vec::new();
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), accessor_f(true), e0);
        assert(out@ =~= Seq::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), accessor_f(true), out@, i as int, e0, ext@),
            children_lt(d@) && arr_in(d@, a@) ==> forall|k: int| 0 <= k < i ==> #[trigger] accessor_f(false)(trees(d@, a@)[k]) == accessor_f(true)(trees(d@, a@)[k]),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        let ghost ob = out@;
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), accessor_f(false), i as int);
                lemma_items_fail(trees(d@, a@), accessor_f(true), i as int);
            }
        }
        match read_accessor(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(e) => return Err(e),
        }
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_step(trees(d@, a@), accessor_f(true), ob, out@, i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), accessor_f(true), out@, e0, ext@);
            lemma_items_eq(trees(d@, a@), accessor_f(false), accessor_f(true));
        }
    }
    Ok(out)
}

pub open spec fn k_accessors() -> Seq<u8> {
    seq![b'a', b'c', b'c', b'e', b's', b's', b'o', b'r', b's']
}

fn read_accessors(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Accessor>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(v) => got(list_s(mt(d@, o@), k_accessors(), accessor_f(true)), v@, old(ext)@, final(ext)@) && list_s(mt(d@, o@), k_accessors(), accessor_f(false))
                == list_s(mt(d@, o@), k_accessors(), accessor_f(true)),
            Err(GltfError::Invalid) => list_s(mt(d@, o@), k_accessors(), accessor_f(false)) is None && list_s(mt(d@, o@), k_accessors(), accessor_f(true)) is None,
            Err(GltfError::Unsupported) => (get_array_s(mt(d@, o@), k_accessors()) matches Some(Some(t)) && exists|k: int|
                0 <= k < t.len() && u_accessor(#[trigger] t[k])) && list_s(mt(d@, o@), k_accessors(), accessor_f(true)) is None,
            Err(_) => false,
        },
{
    proof {
        lemma_ext_refl(ext@);
    }
    match get_array(d, o, &[b'a', b'c', b'c', b'e', b's', b's', b'o', b'r', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_accessors_items(d, a, ext),
    }
}

pub open spec fn buffer_view_f() -> spec_fn(JsonS) -> Option<(BufferView, Ext)> {
    |v: JsonS| buffer_view_s(v)
}

fn read_buffer_views_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<BufferView>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => got(items_s(trees(d@, a@), buffer_view_f()), v@, old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && items_s(trees(d@, a@), buffer_view_f()) is None,
        },
{
    let mut out: Vec<BufferView> = Vec::new();
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), buffer_view_f(), e0);
        assert(out@ =~= Seq::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), buffer_view_f(), out@, i as int, e0, ext@),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        let ghost ob = out@;
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), buffer_view_f(), i as int);
            }
        }
        match read_buffer_view(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_step(trees(d@, a@), buffer_view_f(), ob, out@, i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), buffer_view_f(), out@, e0, ext@);
        }
    }
    Ok(out)
}

fn read_buffer_views(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<BufferView>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(v) => got(list_s(mt(d@, o@), seq![b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w', b's'], buffer_view_f()), v@, old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && list_s(mt(d@, o@), seq![b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w', b's'], buffer_view_f()) is None,
        },
{
    proof {
        lemma_ext_refl(ext@);
    }
    match get_array(d, o, &[b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_buffer_views_items(d, a, ext),
    }
}

pub open spec fn buffer_f() -> spec_fn(JsonS) -> Option<(BufferS, Ext)> {
    |v: JsonS| buffer_s(v)
}

fn read_buffers_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Buffer>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => got(items_s(trees(d@, a@), buffer_f()), buffers_view(v@), old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && items_s(trees(d@, a@), buffer_f()) is None,
        },
{
    let mut out: Vec<Buffer> = Vec::new();
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), buffer_f(), e0);
        assert(buffers_view(out@) =~= Seq::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), buffer_f(), buffers_view(out@), i as int, e0, ext@),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        let ghost ob = buffers_view(out@);
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), buffer_f(), i as int);
            }
        }
        match read_buffer(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_step(trees(d@, a@), buffer_f(), ob, buffers_view(out@), i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), buffer_f(), buffers_view(out@), e0, ext@);
        }
    }
    Ok(out)
}

fn read_buffers(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Buffer>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(v) => got(list_s(mt(d@, o@), seq![b'b', b'u', b'f', b'f', b'e', b'r', b's'], buffer_f()), buffers_view(v@), old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && list_s(mt(d@, o@), seq![b'b', b'u', b'f', b'f', b'e', b'r', b's'], buffer_f()) is None,
        },
{
    proof {
        lemma_ext_refl(ext@);
        assert(buffers_view(Seq::empty()) =~= Seq::empty());
    }
    match get_array(d, o, &[b'b', b'u', b'f', b'f', b'e', b'r', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_buffers_items(d, a, ext),
    }
}

pub open spec fn material_f() -> spec_fn(JsonS) -> Option<(Material, Ext)> {
    |v: JsonS| material_s(v)
}

fn read_materials_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Material>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => got(items_s(trees(d@, a@), material_f()), v@, old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && items_s(trees(d@, a@), material_f()) is None,
        },
{
    let mut out: Vec<Material> = Vec::new();
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), material_f(), e0);
        assert(out@ =~= Seq::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), material_f(), out@, i as int, e0, ext@),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        let ghost ob = out@;
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), material_f(), i as int);
            }
        }
        match read_material(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_step(trees(d@, a@), material_f(), ob, out@, i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), material_f(), out@, e0, ext@);
        }
    }
    Ok(out)
}

fn read_materials(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Material>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(v) => got(list_s(mt(d@, o@), seq![b'm', b'a', b't', b'e', b'r', b'i', b'a', b'l', b's'], material_f()), v@, old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && list_s(mt(d@, o@), seq![b'm', b'a', b't', b'e', b'r', b'i', b'a', b'l', b's'], material_f()) is None,
        },
{
    proof {
        lemma_ext_refl(ext@);
    }
    match get_array(d, o, &[b'm', b'a', b't', b'e', b'r', b'i', b'a', b'l', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_materials_items(d, a, ext),
    }
}

pub open spec fn texture_f() -> spec_fn(JsonS) -> Option<(Texture, Ext)> {
    |v: JsonS| texture_s(v)
}

fn read_textures_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Texture>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => got(items_s(trees(d@, a@), texture_f()), v@, old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && items_s(trees(d@, a@), texture_f()) is None,
        },
{
    let mut out: Vec<Texture> = Vec::new();
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), texture_f(), e0);
        assert(out@ =~= Seq::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), texture_f(), out@, i as int, e0, ext@),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        let ghost ob = out@;
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), texture_f(), i as int);
            }
        }
        match read_texture(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_step(trees(d@, a@), texture_f(), ob, out@, i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), texture_f(), out@, e0, ext@);
        }
    }
    Ok(out)
}

fn read_textures(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Texture>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(v) => got(list_s(mt(d@, o@), seq![b't', b'e', b'x', b't', b'u', b'r', b'e', b's'], texture_f()), v@, old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && list_s(mt(d@, o@), seq![b't', b'e', b'x', b't', b'u', b'r', b'e', b's'], texture_f()) is None,
        },
{
    proof {
        lemma_ext_refl(ext@);
    }
    match get_array(d, o, &[b't', b'e', b'x', b't', b'u', b'r', b'e', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_textures_items(d, a, ext),
    }
}

pub open spec fn image_f() -> spec_fn(JsonS) -> Option<(ImageS, Ext)> {
    |v: JsonS| image_s(v)
}

fn read_images_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Image>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => got(items_s(trees(d@, a@), image_f()), images_view(v@), old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && items_s(trees(d@, a@), image_f()) is None,
        },
{
    let mut out: Vec<Image> = Vec::new();
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), image_f(), e0);
        assert(images_view(out@) =~= Seq::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), image_f(), images_view(out@), i as int, e0, ext@),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        let ghost ob = images_view(out@);
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), image_f(), i as int);
            }
        }
        match read_image(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_step(trees(d@, a@), image_f(), ob, images_view(out@), i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), image_f(), images_view(out@), e0, ext@);
        }
    }
    Ok(out)
}

fn read_images(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Image>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(v) => got(list_s(mt(d@, o@), seq![b'i', b'm', b'a', b'g', b'e', b's'], image_f()), images_view(v@), old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && list_s(mt(d@, o@), seq![b'i', b'm', b'a', b'g', b'e', b's'], image_f()) is None,
        },
{
    proof {
        lemma_ext_refl(ext@);
        assert(images_view(Seq::empty()) =~= Seq::empty());
    }
    match get_array(d, o, &[b'i', b'm', b'a', b'g', b'e', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_images_items(d, a, ext),
    }
}

pub open spec fn camera_f() -> spec_fn(JsonS) -> Option<(Camera, Ext)> {
    |v: JsonS| camera_s(v)
}

fn read_cameras_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Camera>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => got(items_s(trees(d@, a@), camera_f()), v@, old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && items_s(trees(d@, a@), camera_f()) is None,
        },
{
    let mut out: Vec<Camera> = Vec::new();
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), camera_f(), e0);
        assert(out@ =~= Seq::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), camera_f(), out@, i as int, e0, ext@),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        let ghost ob = out@;
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), camera_f(), i as int);
            }
        }
        match read_camera(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_step(trees(d@, a@), camera_f(), ob, out@, i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), camera_f(), out@, e0, ext@);
        }
    }
    Ok(out)
}

fn read_cameras(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Camera>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(v) => got(list_s(mt(d@, o@), seq![b'c', b'a', b'm', b'e', b'r', b'a', b's'], camera_f()), v@, old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && list_s(mt(d@, o@), seq![b'c', b'a', b'm', b'e', b'r', b'a', b's'], camera_f()) is None,
        },
{
    proof {
        lemma_ext_refl(ext@);
    }
    match get_array(d, o, &[b'c', b'a', b'm', b'e', b'r', b'a', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_cameras_items(d, a, ext),
    }
}

pub open spec fn skin_f() -> spec_fn(JsonS) -> Option<(SkinS, Ext)> {
    |v: JsonS| skin_s(v)
}

fn read_skins_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Skin>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => got(items_s(trees(d@, a@), skin_f()), skins_view(v@), old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && items_s(trees(d@, a@), skin_f()) is None,
        },
{
    let mut out: Vec<Skin> = Vec::new();
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), skin_f(), e0);
        assert(skins_view(out@) =~= Seq::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), skin_f(), skins_view(out@), i as int, e0, ext@),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        let ghost ob = skins_view(out@);
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), skin_f(), i as int);
            }
        }
        match read_skin(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(()) => return Err(GltfError::Invalid),
        }
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_step(trees(d@, a@), skin_f(), ob, skins_view(out@), i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), skin_f(), skins_view(out@), e0, ext@);
        }
    }
    Ok(out)
}

fn read_skins(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Skin>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(v) => got(list_s(mt(d@, o@), seq![b's', b'k', b'i', b'n', b's'], skin_f()), skins_view(v@), old(ext)@, final(ext)@),
            Err(e) => e == GltfError::Invalid && list_s(mt(d@, o@), seq![b's', b'k', b'i', b'n', b's'], skin_f()) is None,
        },
{
    proof {
        lemma_ext_refl(ext@);
        assert(skins_view(Seq::empty()) =~= Seq::empty());
    }
    match get_array(d, o, &[b's', b'k', b'i', b'n', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_skins_items(d, a, ext),
    }
}

pub open spec fn animation_f(strict: bool) -> spec_fn(JsonS) -> Option<(AnimationS, Ext)> {
    |v: JsonS| animation_s(v, strict)
}

fn read_animations_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Animation>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(v) => got(items_s(trees(d@, a@), animation_f(true)), animations_view(v@), old(ext)@, final(ext)@) && items_s(trees(d@, a@), animation_f(false))
                == items_s(trees(d@, a@), animation_f(true)),
            Err(GltfError::Invalid) => items_s(trees(d@, a@), animation_f(false)) is None && items_s(trees(d@, a@), animation_f(true)) is None,
            Err(GltfError::Unsupported) => (exists|k: int| 0 <= k < a.len() && u_animation(#[trigger] trees(d@, a@)[k])) && items_s(
                trees(d@, a@),
                animation_f(true),
            ) is None,
            Err(_) => false,
        },
{
    let mut out: Vec<Animation> = Vec::new();
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), animation_f(true), e0);
        assert(animations_view(out@) =~= Seq::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), animation_f(true), animations_view(out@), i as int, e0, ext@),
            children_lt(d@) && arr_in(d@, a@) ==> forall|k: int| 0 <= k < i ==> #[trigger] animation_f(false)(trees(d@, a@)[k]) == animation_f(true)(trees(d@, a@)[k]),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        let ghost ob = animations_view(out@);
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), animation_f(false), i as int);
                lemma_items_fail(trees(d@, a@), animation_f(true), i as int);
            }
        }
        match read_animation(d, a[i], ext) {
            Ok(x) => out.push(x),
            Err(e) => return Err(e),
        }
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_step(trees(d@, a@), animation_f(true), ob, animations_view(out@), i as int, e0, eb, ext@);
            }
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), animation_f(true), animations_view(out@), e0, ext@);
            lemma_items_eq(trees(d@, a@), animation_f(false), animation_f(true));
        }
    }
    Ok(out)
}

pub open spec fn k_animations() -> Seq<u8> {
    seq![b'a', b'n', b'i', b'm', b'a', b't', b'i', b'o', b'n', b's']
}

fn read_animations(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<Vec<Animation>, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(v) => got(list_s(mt(d@, o@), k_animations(), animation_f(true)), animations_view(v@), old(ext)@, final(ext)@) && list_s(mt(d@, o@), k_animations(), animation_f(false))
                == list_s(mt(d@, o@), k_animations(), animation_f(true)),
            Err(GltfError::Invalid) => list_s(mt(d@, o@), k_animations(), animation_f(false)) is None && list_s(mt(d@, o@), k_animations(), animation_f(true)) is None,
            Err(GltfError::Unsupported) => (get_array_s(mt(d@, o@), k_animations()) matches Some(Some(t)) && exists|k: int|
                0 <= k < t.len() && u_animation(#[trigger] t[k])) && list_s(mt(d@, o@), k_animations(), animation_f(true)) is None,
            Err(_) => false,
        },
{
    proof {
        lemma_ext_refl(ext@);
        assert(animations_view(Seq::empty()) =~= Seq::empty());
    }
    match get_array(d, o, &[b'a', b'n', b'i', b'm', b'a', b't', b'i', b'o', b'n', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(Vec::new()),
        Ok(Some(a)) => read_animations_items(d, a, ext),
    }
}

pub open spec fn sampler_f() -> spec_fn(JsonS) -> Option<((), Ext)> {
    |v: JsonS| sampler_s(v)
}

fn check_sampler_items(d: &Vec<JsonNode>, a: &Vec<usize>, ext: &mut Vec<Vec<u8>>) -> (r: Result<(), GltfError>)
    requires
        numbers_wf(d@),
    ensures
        children_lt(d@) && arr_in(d@, a@) ==> match r {
            Ok(_) => (items_s(trees(d@, a@), sampler_f()) matches Some((x, e)) && x.len() == a.len() && ext_grow(old(ext)@, final(ext)@, e)),
            Err(e) => e == GltfError::Invalid && items_s(trees(d@, a@), sampler_f()) is None,
        },
{
    let ghost e0 = ext@;
    let mut i = 0;
    proof {
        lemma_items_init(trees(d@, a@), sampler_f(), e0);
        assert(Seq::new(0, |k: int| ()) =~= Seq::<()>::empty());
    }
    while i < a.len()
        invariant
            numbers_wf(d@),
            e0 == old(ext)@,
            0 <= i <= a.len(),
            children_lt(d@) && arr_in(d@, a@) ==> items_inv(trees(d@, a@), sampler_f(), Seq::new(i as nat, |k: int| ()), i as int, e0, ext@),
        decreases a.len() - i,
    {
        let ghost eb = ext@;
        proof {
            if children_lt(d@) && arr_in(d@, a@) {
                lemma_items_fail(trees(d@, a@), sampler_f(), i as int);
            }
        }
        match read_sampler(d, a[i], ext) {
            Ok(()) => {
                proof {
                    if children_lt(d@) && arr_in(d@, a@) {
                        assert(Seq::new(i as nat, |k: int| ()).push(()) =~= Seq::new((i + 1) as nat, |k: int| ()));
                        lemma_items_step(trees(d@, a@), sampler_f(), Seq::new(i as nat, |k: int| ()), Seq::new((i + 1) as nat, |k: int| ()), i as int, e0, eb, ext@);
                    }
                }
            }
            Err(()) => return Err(GltfError::Invalid),
        }
        i += 1;
    }
    proof {
        if children_lt(d@) && arr_in(d@, a@) {
            lemma_items_done(trees(d@, a@), sampler_f(), Seq::new(a.len() as nat, |k: int| ()), e0, ext@);
        }
    }
    Ok(())
}

fn read_samplers(d: &Vec<JsonNode>, o: &Vec<Member>, ext: &mut Vec<Vec<u8>>) -> (r: Result<u64, GltfError>)
    requires
        numbers_wf(d@),
    ensures
        ctx(d@, o@) ==> match r {
            Ok(n) => (list_s(mt(d@, o@), k_samplers(), sampler_f()) matches Some((x, e)) && x.len() == n && ext_grow(old(ext)@, final(ext)@, e)),
            Err(e) => e == GltfError::Invalid && list_s(mt(d@, o@), k_samplers(), sampler_f()) is None,
        },
{
    proof {
        lemma_ext_refl(ext@);
    }
    match get_array(d, o, &[b's', b'a', b'm', b'p', b'l', b'e', b'r', b's']) {
        Err(()) => Err(GltfError::Invalid),
        Ok(None) => Ok(0),
        Ok(Some(a)) => match check_sampler_items(d, a, ext) {
            Err(e) => Err(e),
            Ok(()) => Ok(a.len() as u64),
        },
    }
}

// MUST-002, MUST-009: asset.version が必要
pub open spec fn asset_s(a: Ms) -> Option<((u64, u64), Option<(u64, u64)>, Ext)> {
    let e = ext_s(a);
    let cp = get_string_s(a, seq![b'c', b'o', b'p', b'y', b'r', b'i', b'g', b'h', b't']);
    let gen = get_string_s(a, seq![b'g', b'e', b'n', b'e', b'r', b'a', b't', b'o', b'r']);
    let ver = match get_string_s(a, seq![b'v', b'e', b'r', b's', b'i', b'o', b'n']) {
        Some(Some(v)) => version_s(v),
        _ => None,
    };
    let minv: Option<Option<(u64, u64)>> = match get_string_s(a, seq![b'm', b'i', b'n', b'V', b'e', b'r', b's', b'i', b'o', b'n']) {
        None => None,
        Some(None) => Some(None),
        Some(Some(v)) => match version_s(v) {
            Some(p) => Some(Some(p)),
            None => None,
        },
    };
    if e is Some && cp is Some && gen is Some && ver is Some && minv is Some {
        Some((ver->Some_0, minv->Some_0, e->Some_0))
    } else {
        None
    }
}

// read_spec(j, is_glb, bin_len)（strict = true が R の規則そのもの）
// MUST-008: asset が必要
pub open spec fn read_spec_m(j: JsonS, strict: bool, is_glb: bool, bin: Option<u64>) -> Option<GltfS> {
    match j {
        JsonS::Object(o) => {
            let e = ext_s(o);
            let asset = match get_object_s(o, seq![b'a', b's', b's', b'e', b't']) {
                Some(Some(a)) => asset_s(a),
                _ => None,
            };
            let eu = string_array_s(o, seq![b'e', b'x', b't', b'e', b'n', b's', b'i', b'o', b'n', b's', b'U', b's', b'e', b'd']);
            let er = string_array_s(o, seq![b'e', b'x', b't', b'e', b'n', b's', b'i', b'o', b'n', b's', b'R', b'e', b'q', b'u', b'i', b'r', b'e', b'd']);
            let scene = get_uint_s(o, seq![b's', b'c', b'e', b'n', b'e']);
            let scenes = list_s(o, seq![b's', b'c', b'e', b'n', b'e', b's'], scene_f());
            let nodes = list_s(o, seq![b'n', b'o', b'd', b'e', b's'], node_f());
            let meshes = list_s(o, seq![b'm', b'e', b's', b'h', b'e', b's'], mesh_f());
            let accessors = list_s(o, k_accessors(), accessor_f(strict));
            let bvs = list_s(o, seq![b'b', b'u', b'f', b'f', b'e', b'r', b'V', b'i', b'e', b'w', b's'], buffer_view_f());
            let bufs = list_s(o, seq![b'b', b'u', b'f', b'f', b'e', b'r', b's'], buffer_f());
            let mats = list_s(o, seq![b'm', b'a', b't', b'e', b'r', b'i', b'a', b'l', b's'], material_f());
            let texs = list_s(o, seq![b't', b'e', b'x', b't', b'u', b'r', b'e', b's'], texture_f());
            let imgs = list_s(o, seq![b'i', b'm', b'a', b'g', b'e', b's'], image_f());
            let smps = list_s(o, k_samplers(), sampler_f());
            let cams = list_s(o, seq![b'c', b'a', b'm', b'e', b'r', b'a', b's'], camera_f());
            let skins = list_s(o, seq![b's', b'k', b'i', b'n', b's'], skin_f());
            let anims = list_s(o, k_animations(), animation_f(strict));
            if e is Some && asset is Some && eu is Some && er is Some && scene is Some && scenes is Some && nodes is Some && meshes
                is Some && accessors is Some && bvs is Some && bufs is Some && mats is Some && texs is Some && imgs is Some
                && smps is Some && cams is Some && skins is Some && anims is Some {
                Some(GltfS {
                    version_major: asset->Some_0.0.0,
                    version_minor: asset->Some_0.0.1,
                    min_version: asset->Some_0.1,
                    extensions_used: eu->Some_0,
                    extensions_required: er->Some_0,
                    scene: scene->Some_0,
                    scenes: scenes->Some_0.0,
                    nodes: nodes->Some_0.0,
                    meshes: meshes->Some_0.0,
                    accessors: accessors->Some_0.0,
                    buffer_views: bvs->Some_0.0,
                    buffers: bufs->Some_0.0,
                    materials: mats->Some_0.0,
                    textures: texs->Some_0.0,
                    images: imgs->Some_0.0,
                    samplers_len: smps->Some_0.0.len() as u64,
                    cameras: cams->Some_0.0,
                    skins: skins->Some_0.0,
                    animations: anims->Some_0.0,
                    extensions_present: e->Some_0.union(asset->Some_0.2).union(scenes->Some_0.1).union(nodes->Some_0.1).union(
                        meshes->Some_0.1,
                    ).union(accessors->Some_0.1).union(bvs->Some_0.1).union(bufs->Some_0.1).union(mats->Some_0.1).union(
                        texs->Some_0.1,
                    ).union(imgs->Some_0.1).union(smps->Some_0.1).union(cams->Some_0.1).union(skins->Some_0.1).union(
                        anims->Some_0.1,
                    ),
                    is_glb,
                    glb_bin_len: bin,
                })
            } else {
                None
            }
        },
        _ => None,
    }
}

// R の規則どおりに読む
pub open spec fn read_spec(j: JsonS, is_glb: bool, bin: Option<u64>) -> Option<GltfS> {
    read_spec_m(j, true, is_glb, bin)
}

// R2: (U) 以外の規則に違反する
pub open spec fn violates_rule(j: JsonS) -> bool {
    read_spec_m(j, false, false, None) is None
}

// R2: (U) の場合を含む（root.accessors の要素、root.animations の要素の samplers の要素）
pub open spec fn contains_u(j: JsonS) -> bool {
    j matches JsonS::Object(o) && ((get_array_s(o, k_accessors()) matches Some(Some(a)) && exists|i: int|
        0 <= i < a.len() && u_accessor(#[trigger] a[i])) || (get_array_s(o, k_animations()) matches Some(Some(an))
        && exists|i: int| 0 <= i < an.len() && u_animation(#[trigger] an[i])))
}

// MUST-002, MUST-008, MUST-009: asset と asset.version が必要
#[verifier::spinoff_prover]
#[verifier::rlimit(200)]
pub fn read_gltf(doc: &JsonDoc, is_glb: bool, glb_bin_len: Option<u64>) -> (r: Result<Gltf, GltfError>)
    requires
        numbers_wf(doc.nodes@),
    ensures
        doc_wf(*doc) ==> match r {
            Ok(g) => read_spec(tree(doc.nodes@, doc.root as int), is_glb, glb_bin_len) == Some(g@),
            Err(GltfError::Unsupported) => contains_u(tree(doc.nodes@, doc.root as int)) && read_spec(tree(doc.nodes@, doc.root as int), is_glb, glb_bin_len) is None,
            Err(GltfError::Invalid) => violates_rule(tree(doc.nodes@, doc.root as int)) && read_spec(tree(doc.nodes@, doc.root as int), is_glb, glb_bin_len) is None,
            Err(_) => false,
        },
{
    let mut extensions_present: Vec<Vec<u8>> = Vec::new();
    let ext = &mut extensions_present;
    let d = &doc.nodes;
    let o = match as_object(d, doc.root) { Ok(o) => o, Err(()) => return Err(GltfError::Invalid) };
    match check_extensions(d, o, ext) { Err(()) => return Err(GltfError::Invalid), Ok(()) => {} }
    let asset = match get_object(d, o, &[b'a', b's', b's', b'e', b't']) { Ok(Some(a)) => a, _ => return Err(GltfError::Invalid) };
    match check_extensions(d, asset, ext) { Err(()) => return Err(GltfError::Invalid), Ok(()) => {} }
    match get_string(d, asset, &[b'c', b'o', b'p', b'y', b'r', b'i', b'g', b'h', b't']) { Err(()) => return Err(GltfError::Invalid), Ok(_) => {} }
    match get_string(d, asset, &[b'g', b'e', b'n', b'e', b'r', b'a', b't', b'o', b'r']) { Err(()) => return Err(GltfError::Invalid), Ok(_) => {} }
    let (version_major, version_minor) = match get_string(d, asset, &[b'v', b'e', b'r', b's', b'i', b'o', b'n']) {
        Ok(Some(v)) => match parse_version(&v) { Some(p) => p, None => return Err(GltfError::Invalid) },
        _ => return Err(GltfError::Invalid),
    };
    let min_version = match get_string(d, asset, &[b'm', b'i', b'n', b'V', b'e', b'r', b's', b'i', b'o', b'n']) {
        Err(()) => return Err(GltfError::Invalid),
        Ok(None) => None,
        Ok(Some(v)) => match parse_version(&v) { Some(p) => Some(p), None => return Err(GltfError::Invalid) },
    };
    let extensions_used = match read_string_array(d, o, &[b'e', b'x', b't', b'e', b'n', b's', b'i', b'o', b'n', b's', b'U', b's', b'e', b'd']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let extensions_required = match read_string_array(d, o, &[b'e', b'x', b't', b'e', b'n', b's', b'i', b'o', b'n', b's', b'R', b'e', b'q', b'u', b'i', b'r', b'e', b'd']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };
    let scene = match get_uint(d, o, &[b's', b'c', b'e', b'n', b'e']) { Ok(v) => v, Err(()) => return Err(GltfError::Invalid) };

    let scenes = match read_scenes(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let nodes = match read_nodes(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let meshes = match read_meshes(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let accessors = match read_accessors(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let buffer_views = match read_buffer_views(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let buffers = match read_buffers(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let materials = match read_materials(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let textures = match read_textures(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let images = match read_images(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let samplers_len = match read_samplers(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let cameras = match read_cameras(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let skins = match read_skins(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    let animations = match read_animations(d, o, ext) { Ok(v) => v, Err(e) => return Err(e) };
    proof {
        if doc_wf(*doc) {
            let j = tree(doc.nodes@, doc.root as int);
            assert(read_spec(j, is_glb, glb_bin_len) is Some);
            let gs = read_spec(j, is_glb, glb_bin_len)->Some_0;
            assert forall|x: Seq<u8>| #[trigger] ext_set(ext@).contains(x) == gs.extensions_present.contains(x) by {
                assert(!ext_set(Seq::<Vec<u8>>::empty()).contains(x));
            }
            assert(ext_set(ext@) =~= gs.extensions_present);
        }
    }
    Ok(Gltf {
        version_major, version_minor, min_version, extensions_used, extensions_required, scene, scenes, nodes, meshes,
        accessors, buffer_views, buffers, materials, textures, images, samplers_len, cameras, skins, animations, extensions_present, is_glb, glb_bin_len,
    })
}

} // verus!
