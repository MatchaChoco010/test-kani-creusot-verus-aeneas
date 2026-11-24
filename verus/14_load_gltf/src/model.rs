use vstd::prelude::*;

verus! {

pub enum GltfError {
    Glb,
    Json,
    Invalid,
    Unsupported,
}

pub struct TextureInfo {
    pub index: u64,
    pub tex_coord: u64,
}

pub struct Material {
    pub base_color_texture: Option<TextureInfo>,
    pub metallic_roughness_texture: Option<TextureInfo>,
    pub normal_texture: Option<TextureInfo>,
    pub occlusion_texture: Option<TextureInfo>,
    pub emissive_texture: Option<TextureInfo>,
}

pub struct Attribute {
    pub name: Vec<u8>,
    pub accessor: u64,
}

pub struct Primitive {
    pub attributes: Vec<Attribute>,
    pub indices: Option<u64>,
    pub material: Option<u64>,
    pub mode: u64,
    pub targets: Vec<Vec<Attribute>>,
}

pub struct Mesh {
    pub primitives: Vec<Primitive>,
    pub weights_len: Option<u64>,
}

pub struct Node {
    pub children: Vec<u64>,
    pub mesh: Option<u64>,
    pub camera: Option<u64>,
    pub skin: Option<u64>,
    pub has_matrix: bool,
    pub has_trs: bool,
    pub weights_len: Option<u64>,
}

pub struct Scene {
    pub nodes: Vec<u64>,
}

pub struct Sparse {
    pub count: u64,
    pub indices_buffer_view: u64,
    pub indices_byte_offset: u64,
    pub indices_component_type: u64,
    pub values_buffer_view: u64,
    pub values_byte_offset: u64,
}

pub struct Accessor {
    pub buffer_view: Option<u64>,
    pub byte_offset: Option<u64>,
    pub component_type: u64,
    pub normalized: bool,
    pub count: u64,
    pub components: u64,
    pub is_matrix: bool,
    pub min_len: Option<u64>,
    pub max_len: Option<u64>,
    pub sparse: Option<Sparse>,
}

pub struct BufferView {
    pub buffer: u64,
    pub byte_offset: u64,
    pub byte_length: u64,
    pub byte_stride: Option<u64>,
    pub target: Option<u64>,
}

pub struct Buffer {
    pub byte_length: u64,
    pub uri: Option<Vec<u8>>,
}

pub struct Image {
    pub uri: Option<Vec<u8>>,
    pub buffer_view: Option<u64>,
    pub has_mime_type: bool,
}

pub struct Texture {
    pub sampler: Option<u64>,
    pub source: Option<u64>,
}

pub struct Camera {
    pub kind: u64,
    pub has_perspective: bool,
    pub has_orthographic: bool,
}

pub struct Skin {
    pub joints: Vec<u64>,
    pub skeleton: Option<u64>,
    pub inverse_bind_matrices: Option<u64>,
}

pub struct Channel {
    pub sampler: u64,
    pub node: Option<u64>,
    pub path: u64,
}

pub struct AnimationSampler {
    pub input: u64,
    pub output: u64,
    pub interpolation: u64,
}

pub struct Animation {
    pub channels: Vec<Channel>,
    pub samplers: Vec<AnimationSampler>,
}

pub struct Gltf {
    pub version_major: u64,
    pub version_minor: u64,
    pub min_version: Option<(u64, u64)>,
    pub extensions_used: Vec<Vec<u8>>,
    pub extensions_required: Vec<Vec<u8>>,
    pub scene: Option<u64>,
    pub scenes: Vec<Scene>,
    pub nodes: Vec<Node>,
    pub meshes: Vec<Mesh>,
    pub accessors: Vec<Accessor>,
    pub buffer_views: Vec<BufferView>,
    pub buffers: Vec<Buffer>,
    pub materials: Vec<Material>,
    pub textures: Vec<Texture>,
    pub images: Vec<Image>,
    pub samplers_len: u64,
    pub cameras: Vec<Camera>,
    pub skins: Vec<Skin>,
    pub animations: Vec<Animation>,
    pub extensions_present: Vec<Vec<u8>>,
    pub is_glb: bool,
    pub glb_bin_len: Option<u64>,
}

pub const KIND_OTHER: u64 = 0;
pub const CAMERA_PERSPECTIVE: u64 = 1;
pub const CAMERA_ORTHOGRAPHIC: u64 = 2;
pub const PATH_TRANSLATION: u64 = 1;
pub const PATH_ROTATION: u64 = 2;
pub const PATH_SCALE: u64 = 3;
pub const PATH_WEIGHTS: u64 = 4;
pub const INTERP_LINEAR: u64 = 0;
pub const INTERP_STEP: u64 = 1;
pub const INTERP_CUBICSPLINE: u64 = 2;

// s[from..to) で最初に b が現れる位置（なければ to）
pub open spec fn first_at(s: Seq<u8>, from: int, to: int, b: u8, r: int) -> bool {
    &&& from <= r <= to
    &&& (r < to ==> s[r] == b)
    &&& forall|k: int| from <= k < r ==> #[trigger] s[k] != b
}

pub open spec fn first_byte(s: Seq<u8>, from: int, to: int, b: u8) -> int {
    choose|r: int| first_at(s, from, to, b, r)
}

pub proof fn lemma_first_byte_unique(s: Seq<u8>, from: int, to: int, b: u8, r: int)
    requires
        first_at(s, from, to, b, r),
    ensures
        first_byte(s, from, to, b) == r,
{
    let r2 = first_byte(s, from, to, b);
    assert(first_at(s, from, to, b, r2));
    if r2 < r {
        assert(s[r2] != b);
    } else if r < r2 {
        assert(s[r] != b);
    }
}

pub fn bytes_eq(a: &[u8], b: &[u8]) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a@[k] == b@[k],
        decreases a.len() - i,
    {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

pub fn opt_eq(a: Option<u64>, b: Option<u64>) -> (r: bool)
    ensures
        r == (a == b),
{
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => x == y,
        _ => false,
    }
}

// 仕様用のモデル（Vec を Seq に、extensions_present を集合にしたもの）
pub struct AttributeS {
    pub name: Seq<u8>,
    pub accessor: u64,
}

pub struct PrimitiveS {
    pub attributes: Seq<AttributeS>,
    pub indices: Option<u64>,
    pub material: Option<u64>,
    pub mode: u64,
    pub targets: Seq<Seq<AttributeS>>,
}

pub struct MeshS {
    pub primitives: Seq<PrimitiveS>,
    pub weights_len: Option<u64>,
}

pub struct NodeS {
    pub children: Seq<u64>,
    pub mesh: Option<u64>,
    pub camera: Option<u64>,
    pub skin: Option<u64>,
    pub has_matrix: bool,
    pub has_trs: bool,
    pub weights_len: Option<u64>,
}

pub struct SceneS {
    pub nodes: Seq<u64>,
}

pub struct BufferS {
    pub byte_length: u64,
    pub uri: Option<Seq<u8>>,
}

pub struct ImageS {
    pub uri: Option<Seq<u8>>,
    pub buffer_view: Option<u64>,
    pub has_mime_type: bool,
}

pub struct SkinS {
    pub joints: Seq<u64>,
    pub skeleton: Option<u64>,
    pub inverse_bind_matrices: Option<u64>,
}

pub struct AnimationS {
    pub channels: Seq<Channel>,
    pub samplers: Seq<AnimationSampler>,
}

pub struct GltfS {
    pub version_major: u64,
    pub version_minor: u64,
    pub min_version: Option<(u64, u64)>,
    pub extensions_used: Seq<Seq<u8>>,
    pub extensions_required: Seq<Seq<u8>>,
    pub scene: Option<u64>,
    pub scenes: Seq<SceneS>,
    pub nodes: Seq<NodeS>,
    pub meshes: Seq<MeshS>,
    pub accessors: Seq<Accessor>,
    pub buffer_views: Seq<BufferView>,
    pub buffers: Seq<BufferS>,
    pub materials: Seq<Material>,
    pub textures: Seq<Texture>,
    pub images: Seq<ImageS>,
    pub samplers_len: u64,
    pub cameras: Seq<Camera>,
    pub skins: Seq<SkinS>,
    pub animations: Seq<AnimationS>,
    pub extensions_present: ISet<Seq<u8>>,
    pub is_glb: bool,
    pub glb_bin_len: Option<u64>,
}

pub open spec fn bytes_opt_view(o: Option<Vec<u8>>) -> Option<Seq<u8>> {
    match o {
        None => None,
        Some(v) => Some(v@),
    }
}

pub open spec fn seq_iset(v: Seq<Seq<u8>>) -> ISet<Seq<u8>> {
    ISet::new(|y: Seq<u8>| v.contains(y))
}

pub open spec fn strings_view(v: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    v.map_values(|b: Vec<u8>| b@)
}

pub open spec fn attrs_view(v: Seq<Attribute>) -> Seq<AttributeS> {
    v.map_values(|a: Attribute| a@)
}

pub open spec fn scenes_view(v: Seq<Scene>) -> Seq<SceneS> {
    v.map_values(|x: Scene| x@)
}

pub open spec fn nodes_view(v: Seq<Node>) -> Seq<NodeS> {
    v.map_values(|x: Node| x@)
}

pub open spec fn meshes_view(v: Seq<Mesh>) -> Seq<MeshS> {
    v.map_values(|x: Mesh| x@)
}

pub open spec fn prims_view(v: Seq<Primitive>) -> Seq<PrimitiveS> {
    v.map_values(|x: Primitive| x@)
}

pub open spec fn buffers_view(v: Seq<Buffer>) -> Seq<BufferS> {
    v.map_values(|x: Buffer| x@)
}

pub open spec fn images_view(v: Seq<Image>) -> Seq<ImageS> {
    v.map_values(|x: Image| x@)
}

pub open spec fn skins_view(v: Seq<Skin>) -> Seq<SkinS> {
    v.map_values(|x: Skin| x@)
}

pub open spec fn animations_view(v: Seq<Animation>) -> Seq<AnimationS> {
    v.map_values(|x: Animation| x@)
}

pub open spec fn targets_view(t: Seq<Vec<Attribute>>) -> Seq<Seq<AttributeS>> {
    t.map_values(|x: Vec<Attribute>| attrs_view(x@))
}

impl View for Attribute {
    type V = AttributeS;

    open spec fn view(&self) -> AttributeS {
        AttributeS { name: self.name@, accessor: self.accessor }
    }
}

impl View for Primitive {
    type V = PrimitiveS;

    open spec fn view(&self) -> PrimitiveS {
        PrimitiveS {
            attributes: attrs_view(self.attributes@),
            indices: self.indices,
            material: self.material,
            mode: self.mode,
            targets: targets_view(self.targets@),
        }
    }
}

impl View for Mesh {
    type V = MeshS;

    open spec fn view(&self) -> MeshS {
        MeshS { primitives: prims_view(self.primitives@), weights_len: self.weights_len }
    }
}

impl View for Node {
    type V = NodeS;

    open spec fn view(&self) -> NodeS {
        NodeS {
            children: self.children@,
            mesh: self.mesh,
            camera: self.camera,
            skin: self.skin,
            has_matrix: self.has_matrix,
            has_trs: self.has_trs,
            weights_len: self.weights_len,
        }
    }
}

impl View for Scene {
    type V = SceneS;

    open spec fn view(&self) -> SceneS {
        SceneS { nodes: self.nodes@ }
    }
}

impl View for Buffer {
    type V = BufferS;

    open spec fn view(&self) -> BufferS {
        BufferS { byte_length: self.byte_length, uri: bytes_opt_view(self.uri) }
    }
}

impl View for Image {
    type V = ImageS;

    open spec fn view(&self) -> ImageS {
        ImageS { uri: bytes_opt_view(self.uri), buffer_view: self.buffer_view, has_mime_type: self.has_mime_type }
    }
}

impl View for Skin {
    type V = SkinS;

    open spec fn view(&self) -> SkinS {
        SkinS { joints: self.joints@, skeleton: self.skeleton, inverse_bind_matrices: self.inverse_bind_matrices }
    }
}

impl View for Animation {
    type V = AnimationS;

    open spec fn view(&self) -> AnimationS {
        AnimationS { channels: self.channels@, samplers: self.samplers@ }
    }
}

impl View for Gltf {
    type V = GltfS;

    open spec fn view(&self) -> GltfS {
        GltfS {
            version_major: self.version_major,
            version_minor: self.version_minor,
            min_version: self.min_version,
            extensions_used: strings_view(self.extensions_used@),
            extensions_required: strings_view(self.extensions_required@),
            scene: self.scene,
            scenes: scenes_view(self.scenes@),
            nodes: nodes_view(self.nodes@),
            meshes: meshes_view(self.meshes@),
            accessors: self.accessors@,
            buffer_views: self.buffer_views@,
            buffers: buffers_view(self.buffers@),
            materials: self.materials@,
            textures: self.textures@,
            images: images_view(self.images@),
            samplers_len: self.samplers_len,
            cameras: self.cameras@,
            skins: skins_view(self.skins@),
            animations: animations_view(self.animations@),
            extensions_present: seq_iset(strings_view(self.extensions_present@)),
            is_glb: self.is_glb,
            glb_bin_len: self.glb_bin_len,
        }
    }
}

} // verus!
