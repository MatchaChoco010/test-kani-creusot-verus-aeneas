
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

pub fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

pub fn opt_eq(a: Option<u64>, b: Option<u64>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => x == y,
        _ => false,
    }
}
