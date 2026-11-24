# Rust の形式検証ツールの比較：Kani・Creusot・Verus・Aeneas

## 1. 概要

### 1.1 目的

Rust の形式検証ツール Kani・Creusot・Verus・Aeneas で同じ題材を検証し、それぞれのツールで何ができて何ができないかを比べる。

### 1.2 評価の基準

各題材について、**対象の関数があるべき性質（事前条件・事後条件）を正しく書き、その性質を満たさないときには検証が失敗する状況を作れたか**で評価する。

- 両方を満たした場合だけを「できた」とする。本来の性質を書けない場合、長さなどの範囲を限ってしか調べられない場合、性質を満たさない実装や呼び出しが拒否されない場合は、「できない」と判定する。部分的にできたという評価はしない。
- 仕様を弱めたり、別の性質に置き換えたり、逃げ道になる仮定を足したりしない。
- 検証で落ちることを確かめた部分は、確かめたあとでコメントアウトし、落ちる理由を添えた。その状態で検証が通ることを確かめてある。
- ツールの既定の機能だけを使う。内部の仕組みを直接参照するような迂回策は使わない。

### 1.3 対象のツールとバージョン

| ツール | バージョン | 方式 |
|---|---|---|
| Kani | 0.68.0 | 有界モデル検査（CBMC） |
| Creusot | 0.14.0 | 演繹的検証（Why3 経由で SMT ソルバー） |
| Verus | 0.2026.11.02.8bf68ee | 演繹的検証（Z3） |
| Aeneas | nightly-2026.11.23-2e3d448（Charon 0.1.322、Lean 4.36.0、Mathlib v4.36.0） | Lean への翻訳と対話的証明 |

### 1.4 リポジトリの構成

```
kani/     01_add_saturate ... 15_pcg_float    （cargo new --lib。ハーネスは #[cfg(kani)] の中。14 はなし）
creusot/  01_add_saturate ... 15_pcg_float    （cargo creusot init。仕様は属性マクロ）
verus/    01_add_saturate ... 15_pcg_float    （cargo verus new --lib。コードは verus! {} の中）
aeneas/   01_add_saturate ... 15_pcg_float    （cargo new --lib。Lean の証明は proofs/ の中）
```

- 各ディレクトリは lib クレートで、`01_add_saturate` ならクレート名は `add_saturate`。
- 14（glTF）は Kani では作っていない。
- Aeneas 版だけ、事前条件のある関数に `debug_assert!` を入れてある（5.2 節）。12・13 では、Creusot・Verus 版のトレイトに仕様用の関数と法則を足した（4.12 節・4.13 節）。それ以外の Rust のコードは、4 ツールで同じにした。

### 1.5 結果の一覧

| # | 題材 | Kani | Creusot | Verus | Aeneas |
|---|---|---|---|---|---|
| 1 | add_saturate | ○ | ○ | ○ | ○ |
| 2 | 事前条件付きの add | ×（事前条件を関数に付けられない。呼び出し側の誤りは、本体のオーバーフローとして見つかるだけ） | ○ | ○ | ○（事前条件を `debug_assert!` で書く） |
| 3 | f32 の clamp01 | ○ | ○（仕様中の f32 リテラルが使えないので定数で書く） | ×（仕様は書けるが、実行コードの比較の結果が仕様の IEEE の比較と結びつかない） | ×（浮動小数点を変換できない） |
| 4 | f32 の add | ×（NaN になる条件は書けるが、±∞ になる条件と丸めは書けない） | ×（NaN / ±∞ の条件も丸めも書けない） | ×（仕様は書けるが、実行コードの演算の結果が仕様の IEEE の演算と結びつかない） | ×（浮動小数点を変換できない） |
| 5 | 生ポインタ | ○（そのまま） | ○（`Perm`） | ○（`PPtr` と `PointsTo`） | ×（生ポインタの参照外しは非対応） |
| 6 | ループ（max） | ×（展開できる長さまでしか調べられない） | ○ | ○ | ○ |
| 7 | iter_mut | ×（展開できる長さまでしか調べられない） | ○ | ○ | ○ |
| 8 | ジェネリクス | ×（汎用の関数を検証できない。型ごと・長さを限ってしか調べられない） | ○ | ○ | ○ |
| 9 | ジェネリクス + `==` | ×（汎用の関数を検証できない。型ごと・長さを限ってしか調べられない） | ×（f32 版を書けない） | ×（f32 版を書けない） | ×（f32 版を変換できない） |
| 10 | Counting to 2 | ×（スレッドで内部エラー） | ○ | ×（「結果は 2」を書けない。書けるのは「join が成功すれば 2」まで） | ×（共有カウンタの更新がモデルに現れない） |
| 11 | 証明の誘導 | ×（誘導の仕組みがない。長さを限ってしか調べられない） | ○ | ○ | ○ |
| 12 | 分割して畳み込む関数 | ×（汎用の関数を検証できず、事前条件を呼び出し側に課せない） | ○ | ○ | ×（事前条件の法則を `assert!` で書けず、定理の仮定は呼び出し側に課されない） |
| 13 | 外部ライブラリを信用する | ×（仕様を宣言して信用できない。スタブで実装を差し替えるだけで、事前条件も書けない） | ○ | ○ | ○（本体を外し、axiom で仕様を信用する） |
| 14 | glTF の読み込み | － | ○（JSON の木をアリーナにし、パーサーの相互再帰をなくす必要があった） | ○ | ○（ループを小さな関数に切り出す必要があった） |
| 15a | PCG64（パニックしない・周期 2^128・各値 2^64 回） | ×（周期を書けない。ループを 2^128 回展開できない） | ○ | ○ | ○ |
| 15b | u64 → [0, 1) の f32（NaN・±∞ なし、範囲） | ○ | ×（整数→f32 の変換と `from_bits` を翻訳できない） | ×（実行コードの f32 の演算が仕様の IEEE の演算と結びつかない） | ×（浮動小数点を変換できない） |
| 15c | u64 → [0, 1) の f32（間隔を考慮した一様性） | ×（個数・確率を書けない） | ×（整数→f32 の変換と `from_bits` を翻訳できない） | ×（実行コードの f32 の演算が仕様の IEEE の演算と結びつかない） | ×（浮動小数点を変換できない） |

○ = 持つべき性質を書いて検証でき、性質を満たさない実装や呼び出しは検証で拒否される、× = できない（括弧内は理由）、－ = 対象外。

## 2. 各ツールの検証の仕組み

### 2.1 Kani

- 有界モデル検査器。Rust のコードを CBMC に渡し、SAT / SMT ソルバーで網羅的に調べる。
- 仕様は「ハーネス」（`#[kani::proof]` を付けた関数）に書く。`kani::any()` で任意の値を作り、`kani::assume` で入力を絞り、`assert!` で性質を確かめる。
- ループは決められた回数（`#[kani::unwind(n)]`）まで展開する。展開しきれない場合は失敗として報告する。
- f32 をビット単位の IEEE 754 として正確に扱い、反例も出せる。
- 関数に仕様を付ける安定した構文はない（関数の契約は不安定機能で、このリポジトリでは使わない）。そのため、呼び出し側に事前条件を課すことはできず、本体を実際にたどって誤りを見つける。

### 2.2 Creusot

- 仕様を属性マクロ（`#[requires]`、`#[ensures]`、`#[invariant]` など）で書き、仕様言語 pearlite で記述する。
- Why3 を経由して、複数の SMT ソルバー（Alt-Ergo、Z3、CVC5 など）で検証条件を証明する。
- `x@` は値の数学的なモデル（ビュー）、`^x` は可変参照の最終値（prophecy）。
- クレート内のすべての関数を検証する。

### 2.3 Verus

- `verus! { ... }` の中に、仕様付きの Rust を書く。`requires`、`ensures`、`returns`、`invariant`、`decreases` に加え、`spec fn`（仕様用の関数）、`proof fn`（補題）、ゴースト値（`Ghost`、`Tracked`）がある。
- Z3 で検証する。非線形算術は既定で無効で、ループは前の事実を引き継がない。そのため、補助の記述を明示的に書く場面が多い。
- クレート内の `verus!` の中のすべての関数を検証する。

### 2.4 Aeneas

- Charon が Rust のクレートを中間表現（LLBC）に変換し、Aeneas がそれを Lean の関数に翻訳する。仕様は、生成された関数についての Lean の定理として、別ファイルに書く。Rust 側に仕様言語はない。
- 翻訳された関数は `Result` を返し、オーバーフロー・範囲外アクセス・`assert!` の失敗は `fail` になる。`f x ⦃ r => P r ⦄` は「`f x` が失敗せずに値 `r` を返し、`P r` が成り立つ」という意味。
- 関数の仕様は、`@[step]` を付けた定理として書く。定理の仮定が事前条件、`⦃ ⦄` の中が事後条件になる（`documentation/aeneas-overview.md` 4.1・4.2）。`@[step]` で登録した仕様は、呼び出し側の証明で `step` が自動的に使う。
- 証明は Lean の tactic で書く。主に使うのは次の 2 つで、SMT ソルバーは使わない。
  - `step*`: モナドの中の呼び出しを、登録済みの仕様で 1 つずつ処理する。
  - `agrind`: Aeneas 版の `grind`。`@[agrind]` を付けた補題だけを使う。Aeneas のドキュメント（`tactics-reference.md`）は、`grind` は文脈の展開が制御しにくいので `agrind` を使うよう勧めている。
- ループは `-loops-to-rec` で再帰関数に翻訳した。Aeneas のドキュメント（`tips-and-tricks.md`）は、証明を書くプロジェクトにはこちらを勧めている。既定の `loop` 結合子は「証明の基盤がまだ成熟していない」とされている。
- 浮動小数点、unsafe（生ポインタ）、並行処理は非対応（4.3 節・4.5 節・4.10 節）。

## 3. インストールと実行

各ツールの公式の手順でインストールした。どのツールも rustup が必要（Aeneas では Charon のビルドに使う）。

```sh
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```

### 3.1 Kani

```sh
cargo install --locked kani-verifier --version 0.68.0
cargo kani setup
```

- `cargo kani setup` は、CBMC などを含むバンドルを `~/.kani/` に展開し、Kani が使う nightly ツールチェインを rustup で入れる。
- プロジェクトは普通の Cargo プロジェクトでよい。`kani` クレートは `cargo kani` が自動で注入する。
- ハーネスを `#[cfg(kani)]` で囲むので、通常のビルドで `unexpected_cfgs` の警告が出ないよう、`Cargo.toml` に次を足す。

  ```toml
  [lints.rust]
  unexpected_cfgs = { level = "warn", check-cfg = ['cfg(kani)'] }
  ```

- 不安定機能は、`Cargo.toml` の `[package.metadata.kani]` で、クレートごとに有効にする（13 の `unstable = { stubbing = true }`）。

### 3.2 Creusot

1. opam をインストールする。

   ```sh
   sudo dnf install opam
   opam init
   ```

2. Creusot をクローンし、`INSTALL` スクリプトを実行する。

   ```sh
   git clone --branch v0.14.0 https://github.com/creusot-rs/creusot
   cd creusot
   ./INSTALL
   ```

   `INSTALL` は次の処理を行う。

   - `~/.local/share/creusot/_opam` に専用の opam switch を作り、OCaml・Why3・why3-ide・why3find をビルドする。途中で opam がシステムパッケージ（depext）を `dnf` で入れるか尋ねるので、許可する。Fedora では `gtk3-devel`、`gtksourceview3-devel`、`zlib-ng-compat-static` が求められる。先に `sudo dnf install gtk3-devel gtksourceview3-devel zlib-ng-compat-static` を実行しておいてもよい。
   - Alt-Ergo、Z3、CVC4、CVC5 をダウンロードする。
   - `cargo-creusot`、`creusot-rustc`、Why3 の設定ファイル（`~/.config/creusot/why3.conf`）をインストールする。

3. `cargo creusot --help` で、インストールできたか確かめる。

プロジェクトは `cargo creusot new <名前>`（現在のディレクトリに作るなら `cargo creusot init <名前>`）で作る。既定は lib クレートで、`creusot-std = "0.14.0"` への依存、`why3find.json`、`cfg(creusot)` の lint 設定が生成される。

### 3.3 Verus

1. GitHub の Releases から、プラットフォーム用の zip をダウンロードして展開する。

   ```sh
   gh release download release/0.2026.11.02.8bf68ee -R verus-lang/verus -p 'verus-0.2026.11.02.8bf68ee-x86-linux.zip'
   unzip verus-0.2026.11.02.8bf68ee-x86-linux.zip
   ```

2. 展開したディレクトリで `./verus --version` を実行する。必要な Rust ツールチェインがなければ、インストールするコマンドが表示されるので、それを実行する。このバージョンでは次のコマンドになる。

   ```sh
   rustup install 1.99.1-x86_64-unknown-linux-gnu
   ```

3. 展開したディレクトリ（`verus` と `cargo-verus` がある）を `PATH` に追加する。

プロジェクトは `cargo verus new --lib <名前>` で作る。`vstd` への依存と `[package.metadata.verus] verify = true` が生成される。

- `cargo verus new` は、ディレクトリ名とクレート名を同じにする。数字で始まる名前はクレート名にできないので、`cargo verus new --lib add_saturate` で作ってからディレクトリ名を変えた。
- `cargo new` と違って親の Git リポジトリを検出せず、プロジェクトごとに入れ子の `.git` を作る。このリポジトリでは、作成後に削除した。

### 3.4 Aeneas

Aeneas には OCaml（opam）、Rust（rustup）、Lean（elan）が必要。

1. opam で OCaml 5.3.0 の switch を作る（opam のインストールは 3.2 節の手順 1 と同じ）。

   ```sh
   opam switch create 5.3.0
   eval $(opam env --switch=5.3.0)
   ```

2. Aeneas をクローンし、OCaml の依存を入れる。

   ```sh
   git clone --branch nightly-2026.11.23-2e3d448 https://github.com/AeneasVerif/aeneas
   cd aeneas
   opam install ./src --deps-only --with-test
   ```

3. Charon を用意する。`make setup-charon` は、`charon-pin` に書かれたコミットで Charon を `./charon` にクローンしてビルドする。Aeneas が使う Charon の OCaml ライブラリの依存は、Charon の README の手順で `charon` ディレクトリから入れる。

   ```sh
   make setup-charon
   cd charon
   opam install . --deps-only --with-test
   make build-charon-rust       # rustup でビルドする。bin/charon ができる
   cd ..
   ```

4. Aeneas をビルドする。`bin/aeneas` ができる。

   ```sh
   make
   ```

5. Lean のツールチェイン管理ツール elan を入れる（Lean 公式の手順）。

   ```sh
   curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
   ```

6. `aeneas/charon/bin`（`charon`）と `aeneas/bin`（`aeneas`）を `PATH` に追加する。

プロジェクトは 2 つの部分からなる。

- **Rust のクレート:** `cargo new --lib` で作る。Aeneas 用の依存や属性は要らない。
- **Lean のプロジェクト:** クレートの中の `proofs/` に、Aeneas の README の「Lean バックエンドの追加手順」に従って作る。

  ```sh
  cd proofs
  lake init <名前> lib
  cp <aeneas>/backends/lean/lean-toolchain .
  ```

  `lakefile.toml` には、Aeneas への依存と、Lake のローカル成果物キャッシュを有効にする設定を書き足す。

  ```toml
  defaultTargets = ["<名前>"]
  enableArtifactCache = true      # 追加

  [[lean_lib]]
  name = "<名前>"

  [[require]]                     # 追加
  name = "aeneas"
  git = "https://github.com/AeneasVerif/aeneas.git"
  rev = "2e3d4488280bb8a95411db81019a7854a784861f"
  subDir = "backends/lean"
  ```

  Aeneas の Lean ライブラリは、GitHub の Aeneas のリポジトリの、使ったバージョン（`nightly-2026.11.23-2e3d448`）のコミットで参照する。手元のクローンを `path` で参照すると、`lakefile.toml` と `lake-manifest.json` に、その環境の絶対パスが入る。

  ビルドは次のとおり。`lake exe cache get` は、最初の 1 プロジェクトでだけ実行する。

  ```sh
  lake exe cache get    # Mathlib のビルド済みファイルを取得する
  lake build
  ```

- `lake init` は、`<名前>/Basic.lean`（`def hello := "world"` だけの雛形）、`README.md`、`.github/workflows/lean_action_ci.yml` も作る。このリポジトリでは、これらを削除した（`.github` は、リポジトリのルートになければ GitHub Actions に使われない）。既存の Git リポジトリの中で実行した場合、入れ子の `.git` は作られない。
- `enableArtifactCache = true` を書くと、ビルド成果物が Lean のツールチェインごとのキャッシュ（`~/.elan/toolchains/<ツールチェイン>/lake/cache`）に登録され、各プロジェクトの `.lake/` とハードリンクで共有される（Lake の `PackageConfig` の説明）。
  - 最初のプロジェクトで `lake exe cache get` と `lake build` を実行すると、ビルドに使われた Mathlib の成果物（Aeneas が import する約 1200 モジュール）がキャッシュに入る。
  - 2 つ目以降のプロジェクトは、Mathlib を再ビルドせずにキャッシュから使える。
  - ただし、`lake-manifest.json` のない新しいプロジェクトで最初に `lake build` すると、依存を解決するときに Mathlib の post-update フック（`info: mathlib: running post-update hooks`）が `lake exe cache get` と同じ取得を行い、Mathlib 全体を `.lake/packages` に展開する（`.lake/` が約 7.4GB になる）。12 を追加したときに確かめた。そのあと `.lake/` を消して `lake build` し直すと、`lake-manifest.json` があるのでフックは走らず、キャッシュを共有する形になる。
  - このリポジトリでは、キャッシュができたあとで最初のプロジェクトの `.lake/` も消して `lake build` し直し、10 個のプロジェクトすべてがキャッシュを共有する形にした。ダウンロードした圧縮ファイル（`~/.cache/mathlib`）は、これで不要になったので削除した。キャッシュと 10 個の `.lake/` を合わせて約 5.7GB。

### 3.5 実行コマンド

| ツール | 検証 | 通常ビルド |
|---|---|---|
| Kani | `cargo kani` | `cargo build` |
| Creusot | `cargo creusot` | `cargo build` |
| Verus | `cargo verus verify` | `cargo verus build` |
| Aeneas | `charon cargo --preset=aeneas` → `aeneas -backend lean <クレート名>.llbc -dest proofs -subdir /<名前>/Code -split-files -namespace <名前> -loops-to-rec` → `proofs/` で `lake build` | `cargo build` |

- Aeneas が生成したコードは `proofs/<名前>/Code/` に置かれる。証明は `proofs/<名前>/Properties.lean` に手で書く。
- `-split-files` を付けると、外部の関数（Aeneas の Lean ライブラリにモデルがない標準ライブラリやクレートの関数）が、`FunsExternal_Template.lean` に axiom として列挙される。これを `FunsExternal.lean` にコピーして使う（README の手順）。

### 3.6 うまく動かなかった点と対処

**Creusot**

- **`cargo creusot clean` が止まる:** 関数を消したあと、`verif/` に古い証明ファイルが残り、`Warning: found dangling files and directories` と警告された。`cargo creusot clean` で消せるが、このコマンドは確認の入力を待つので、端末から対話的に実行する必要がある。
- **`atomic_sc` が見つからない:** `cargo creusot init` が作る `Cargo.toml` のままでは、`creusot_std::std::sync::atomic_sc` が `cannot find atomic_sc in sync`（`the item is gated behind the sc-drf feature`）になった。`creusot-std = { version = "0.14.0", features = ["sc-drf"] }` として解決した（10 章）。
- **論理関数の本体で `@` が使えない:** `#[logic]` の本体で `s[0]@` と書くと、`expected one of ... found @` でコンパイルできなかった。論理関数の本体の pearlite の構文は、`pearlite! { ... }` で包む必要がある（4.13 節）。
- **仕様のない関数だけのクレートで `cargo creusot` が失敗する:** 04 で仕様をすべて外すと、`creusot_std::prelude` の import が未使用になる。import を消すと `cargo creusot` が `unused dependency creusot-std` で失敗し、残すと通常ビルドで `unused import` の警告が出た。`use creusot_std as _;` とすると、どちらも出なくなった。

**Verus**

- **`tokenized_state_machine!` が見つからない:** `cargo verus new` が作る `Cargo.toml` は `vstd` にしか依存せず、`use verus_state_machines_macros::tokenized_state_machine;` を解決できなかった。vstd はこのマクロを再エクスポートしていない。`verus_state_machines_macros = "=0.0.0-2026-11-01-0251"`（vstd と同じバージョン）を依存に足して解決した（10 章）。

**Aeneas**

- **`opam install src` が失敗する:** README の `opam install src --deps-only --with-test` は `No package named src found` で失敗した。opam は `./` の付かない名前をパッケージ名として扱うので、`opam install ./src --deps-only --with-test` と書く。
- **nix でビルドした Charon が動かない:** `make setup-charon`（`scripts/check-charon-install.sh`）は、nix が入っていれば rustup より nix を優先し、`nix develop` の中で Charon をビルドする。できた `charon-driver` は nix ストアの glibc と `librustc_driver` にリンクされていて、nix の外では `libz.so.1: cannot open shared object file` などのエラーで起動しなかった。Charon の README にある rustup の手順（`charon` ディレクトリで `make build-charon-rust`）でビルドし直して解決した。
- **Aeneas の `make` が `Library "ppx_deriving_hash" not found` で失敗する:** Aeneas が使う Charon の OCaml ライブラリ（`charon-ml`）の依存は、`charon` 側の opam ファイルに書かれている。nix でビルドした場合、これらは nix の環境にしか入らない。`charon` ディレクトリで `opam install . --deps-only --with-test` を実行して解決した。
- **Lean のプロジェクトが 1 つあたり約 7.4GB になる:** Lake の既定では、依存は各プロジェクトの `.lake/packages` に置かれる（Lake の README の `packagesDir`）。`lake exe cache get` は Mathlib 全体（約 8700 モジュール、展開後 6.8GB）を各プロジェクトに展開するので、9 プロジェクトで約 67GB になった。ダウンロードした圧縮ファイル（約 460MB）は共有されるが、展開後のファイルは共有されない。Lake のローカル成果物キャッシュ（`enableArtifactCache = true`）で解決した。この設定は既定では無効で、既定の Lake は「キャッシュを読めるが書き込まない」。
- **名前空間 `Add` / `Max` が衝突する:** `-namespace Add` で生成すると、`lake build` が ``invalid declaration name `add`, structure `Add` has field `add` `` で失敗した。生成した関数 `Add.add` が、Lean の標準の型クラス `Add` のフィールドと衝突する。06 の `Max`（`Max.max`）も同じなので、名前空間を `AddCrate`、`MaxCrate` にした。
- **トレイト名 `Monoid` が Mathlib と衝突する:** 12 の `Properties.lean` で `open FoldHalves` のあとに `Monoid T` と書くと、`Ambiguous term Monoid`（Mathlib の `_root_.Monoid` と、生成された `FoldHalves.Monoid`）になった。定理では `FoldHalves.Monoid T` と書いた。13 では、Aeneas が生成した `FunsExternal_Template.lean` そのものが同じ理由でビルドできず、コピーした `FunsExternal.lean` で `ParSum.Monoid` と書いた（4.13 節）。

## 4. 題材ごとの結果

### 4.1 整数の add_saturate（`01_add_saturate`）

**関数と仕様:** `add_saturate(a: u32, b: u32) -> u32` は、`a + b` が `u32::MAX` 以下ならその和を、超えるなら `u32::MAX` を返す。実装は 4 ツールで同じ。

```rust
pub fn add_saturate(a: u32, b: u32) -> u32 {
    if a > u32::MAX - b { u32::MAX } else { a + b }
}
```

Creusot と Verus のガイドには、場合分けのある事後条件の書き方の推奨がない。そこで、それぞれの標準ライブラリ（creusot-std / vstd）が `u32::saturating_add` に付けている仕様の書き方に合わせた。

#### Kani

```rust
#[cfg(kani)]
#[kani::proof]
fn check_add_saturate() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    let r = add_saturate(a, b);
    assert_eq!(r as u64, (a as u64 + b as u64).min(u32::MAX as u64));
}
```

- 期待値は、u64 で計算した和を `u32::MAX` で頭打ちにした値。u32 どうしの和は u64 で正確に表せるので、この u64 は数学の和として使える。
- 算術オーバーフローは、ハーネスに書かなくても Kani が自動で検査する。
- 結果: `VERIFICATION:- SUCCESSFUL`

#### Creusot

```rust
#[ensures(a@ + b@ <= u32::MAX@ ==> result@ == a@ + b@)]
#[ensures(a@ + b@ > u32::MAX@ ==> result@ == u32::MAX@)]
pub fn add_saturate(a: u32, b: u32) -> u32
```

- creusot-std の `saturating_add`（`creusot-std/src/std/num.rs` 405〜417 行）が、「場合 `==>` 結果」の `#[ensures]` を場合の数だけ並べているので、それに合わせた。
- 複数の `#[ensures]` は連言として扱われ、Why3 の検証条件では節ごとに別の名前が付く。どの場合で失敗したかが分かれて見える。
- Creusot は場合分けの網羅性を検査しない。ここでは 2 つの条件が互いに補集合になっている。
- `@` は値を数学の整数に写す演算子で、仕様の `a@ + b@` はオーバーフローしない。
- 結果: `Proved (verif/add_saturate_rlib/add_saturate.coma) ✔`

#### Verus

```rust
pub fn add_saturate(a: u32, b: u32) -> u32
    returns
        (if a + b > u32::MAX { u32::MAX } else { (a + b) as u32 }),
```

- vstd の `u32::saturating_add`（`vstd/std_specs/num.rs` 251〜258 行）が、この `returns (if ...)` の形をしている。
- `returns e` は「戻り値は `e` に等しい」という事後条件（ガイド `reference-exec-signature.md`）。戻り値が入力から一意に決まる関数は `returns`、部分的な性質は `ensures` で書く。
- 仕様の中の `a + b` は数学の整数の演算になるので、`@` に当たる変換は要らない。
- 結果: `verification results:: 1 verified, 0 errors`

#### Aeneas

生成された Lean の関数:

```lean
def add_saturate (a : Std.U32) (b : Std.U32) : Result Std.U32 := do
  let i ← core.num.U32.MAX - b
  if a > i
  then ok core.num.U32.MAX
  else a + b
```

仕様と証明:

```lean
attribute [local agrind =] U32.rMax UScalar.ofNatCore_val_eq

theorem add_saturate_spec (a b : U32) :
    add_saturate a b ⦃ r =>
      (a.val + b.val ≤ U32.max → r.val = a.val + b.val) ∧
      (U32.max < a.val + b.val → r.val = U32.max) ⦄ := by
  unfold add_saturate
  step*
```

- `.val` は自然数の値で、Creusot の `@` に当たる。
- `core.num.U32.MAX` は `UScalar.ofNat U32.rMax` と定義され、`U32.rMax` は 4294967295 と定義された自然数になっている。この値を `agrind` が使えるように、`attribute [local agrind =]` で登録した（Aeneas のドキュメントにある、定数を solver に登録する方法）。登録しないと、`agrind` が `U32.MAX` の値を知らずに失敗した。
- 結果: `Build completed successfully`

### 4.2 事前条件付きの add（`02_add`）

**関数と仕様:**

- `add(a, b)`: 事前条件は「`a + b` が u32 に収まる」、事後条件は「結果は `a + b`」。
- `double(a)`: `add(a, a)` を無条件に呼ぶ。`a` に制約がないので、`add` の事前条件を満たせない。この関数が検証で弾かれることを確かめる。
- `double_checked(a)`: `a <= u32::MAX / 2` を確かめてから `add(a, a)` を呼ぶ。事後条件は「`a <= u32::MAX / 2` なら `Some(2a)`、そうでなければ `None`」。

`double` が検証で落ちることを確かめたあと、その部分をコメントアウトした。

#### Kani

**書けない。** 事前条件を関数に付けて、呼び出し側に課す方法がない。`double` の誤りは、`add` の本体がオーバーフローするので見つかるだけである。

```rust
#[cfg(kani)]
#[kani::proof]
fn check_add() {
    let a: u32 = kani::any();
    let b: u32 = kani::any();
    kani::assume(a as u64 + b as u64 <= u32::MAX as u64);
    assert_eq!(add(a, b) as u64, a as u64 + b as u64);
}

#[cfg(kani)]
#[kani::proof]
fn check_double_checked() {
    let a: u32 = kani::any();
    let r = double_checked(a);
    if a <= u32::MAX / 2 {
        assert_eq!(r, Some(a * 2));
    } else {
        assert_eq!(r, None);
    }
}
```

- Kani の安定した機能には `requires` がないので、`kani::assume` で入力を絞る。関数の契約（`kani::requires`）は不安定機能で、このリポジトリでは使わない。
- `double` を呼ぶハーネス（コメントアウト済み）は `Failed Checks: attempt to add with overflow` で失敗する。Kani は事前条件を見るのではなく、`add` の本体までたどって `a + a` のオーバーフローを見つける。事前条件が本体のオーバーフローと一致しているので検出できるが、本体で失敗しない事前条件は検出できない。
- 結果: `Complete - 2 successfully verified harnesses, 0 failures, 2 total.`

#### Creusot

```rust
#[requires(a@ + b@ <= u32::MAX@)]
#[ensures(result@ == a@ + b@)]
pub fn add(a: u32, b: u32) -> u32

#[ensures(a@ <= u32::MAX@ / 2 ==> match result { Some(r) => r@ == 2 * a@, None => false })]
#[ensures(a@ > u32::MAX@ / 2 ==> result == None)]
pub fn double_checked(a: u32) -> Option<u32>
```

- `double` があると `Goal Coma.vc_double: ✘` で失敗する。Creusot はクレート内のすべての関数を検証するので、関数ごとコメントアウトした。
- 結果: `Proved (2 files) ✔`

#### Verus

```rust
pub fn add(a: u32, b: u32) -> (r: u32)
    requires
        a + b <= u32::MAX,
    ensures
        r == a + b,

pub fn double_checked(a: u32) -> Option<u32>
    returns
        (if a <= u32::MAX / 2 { Some((2 * a) as u32) } else { None }),
```

- `double` があると `error: precondition not satisfied` になり、`add(a, a)` の行と、満たせなかった `requires` の両方が表示される。関数ごとコメントアウトした。
- 結果: `verification results:: 2 verified, 0 errors`

#### Aeneas

Aeneas 版では、`add` の事前条件を `debug_assert!` で Rust のコードに書いた。理由は 5.2 節で述べる。

```rust
pub fn add(a: u32, b: u32) -> u32 {
    debug_assert!(a <= u32::MAX - b);
    a + b
}
```

生成されたコードでは、`debug_assert!` が `massert`（条件が偽なら失敗する）になる。

```lean
def add (a : Std.U32) (b : Std.U32) : Result Std.U32 := do
  let i ← core.num.U32.MAX - b
  massert (a <= i)
  a + b
```

```lean
@[step]
theorem add_spec (a b : U32) (h : a.val + b.val ≤ U32.max) :
    add a b ⦃ c => c.val = a.val + b.val ⦄ := by
  unfold add
  step*

-- 証明失敗: a に制約が無いので add の事前条件 a + a ≤ U32.max を示せない
-- theorem double_spec (a : U32) :
--     double a ⦃ _ => True ⦄ := by
--   unfold double
--   step*

theorem double_checked_spec (a : U32) :
    double_checked a ⦃ r => match r with
      | some c => a.val ≤ U32.max / 2 ∧ c.val = 2 * a.val
      | none => U32.max / 2 < a.val ⦄ := by
  unfold double_checked
  step*
```

- `double_spec` は `unsolved goals case h ⊢ ↑a + ↑a ≤ U32.max` で失敗する。`add` の定義を展開して証明しようとしても、`debug_assert!` の条件 `⊢ a ≤ i` が残って失敗する。
- Aeneas では検証を Lean の定理で行うので、`double` は Rust のコードに残し、失敗する定理だけをコメントアウトした。
- 結果: `Build completed successfully`

### 4.3 浮動小数点数の clamp01（`03_clamp01`）

**関数と仕様:** `clamp01(x: f32) -> f32` は、`x < 0` なら 0、`x > 1` なら 1、どちらでもなければ `x` をそのまま返す。NaN はどちらの比較も偽になるので、NaN がそのまま返る。

```rust
pub fn clamp01(x: f32) -> f32 {
    if x < 0.0 {
        0.0
    } else if x > 1.0 {
        1.0
    } else {
        x
    }
}
```

#### Kani

```rust
let x: f32 = kani::any();
let r = clamp01(x);
if x < 0.0 {
    assert!(r == 0.0);
} else if x > 1.0 {
    assert!(r == 1.0);
} else {
    assert_eq!(r.to_bits(), x.to_bits());
}
```

- CBMC は IEEE 754 をビット単位で正確に扱うので、NaN・±∞・±0 を含むすべての f32 を調べられる。
- 3 番目の場合は、`r == x`（IEEE の比較）ではなくビット列の一致で書いた。`r == x` だと NaN のときに偽になるが、関数は NaN をそのまま返しているので、仕様としてはビット列が同じことを確かめるのが正しい。
- 結果: `VERIFICATION:- SUCCESSFUL`

#### Creusot

```rust
// pearlite は f32 リテラルを翻訳できない (Unsupported literal)。定数は const 評価を経て翻訳されるので定数で参照する
const ZERO: f32 = 0.0;
const ONE: f32 = 1.0;

#[ensures(x < ZERO ==> result == ZERO)]
#[ensures(x > ONE ==> result == ONE)]
#[ensures(!(x < ZERO) && !(x > ONE) ==> result == x)]
pub fn clamp01(x: f32) -> f32
```

- **f32 のモデル:** f32 は Why3 の `ieee_float.Float32`（IEEE 754 binary32）に翻訳され、実行コードの演算は最近接偶数丸め（RNE）、比較は IEEE の比較になる（`prelude-generator/float.coma`）。
- **仕様で使えるもの:** f32 について仕様で使えるのは、creusot-std の `PartialOrdLogic for f32`（`creusot-std/src/logic/ord.rs` 258〜280 行）が定める `<`（IEEE の `<`）と、そこから定義される `>` / `<=` / `>=` だけ。
- **仕様の `==`:** 論理的な等しさ（同じ値か）で、IEEE の `==` ではない。そのため、`result == x` は NaN でも成り立つ。
- 3 番目の条件を否定形で書いたのは、`ZERO <= x` と書くと `-0.0` がどの場合にも入らなくなるため（`<=` は「`<` または論理的に等しい」と定義され、`0.0` と `-0.0` は論理的に別の値）。
- **f32 リテラルを定数で書いている理由:** 仕様の中に `0.0f32` と書くと、内部コンパイラエラーになる。

  ```
  error: internal compiler error: Unsupported literal
   --> src/lib.rs:3:15
    |
  3 | #[ensures(x < 0.0f32 ==> result == 0.0f32)]
  ```

  pearlite のリテラルを翻訳する処理（`creusot/src/translation/pearlite/from_thir.rs` 298〜321 行）が、Bool・整数・Char しか扱っていないため。一方、定数は rustc の定数評価の結果を翻訳する別の経路（`creusot/src/translation/constant.rs` 131〜144 行）があるので、定数として参照すれば翻訳できる。ドキュメントにはどちらの記述もない。
- 結果: `Proved (verif/clamp01_rlib/clamp01.coma) ✔`

#### Verus

**書けるが、証明できない。** 仕様の側には IEEE の比較がある（`x.ieee_lt(0.0f32)` など。`builtin/src/lib.rs` の `IeeeFloat` トレイト）。しかし、実行コードの比較 `x < 0.0` の結果は vstd が未解釈関数でしか表さず、仕様の IEEE の比較と結びついていない。`ieee_lt` / `ieee_gt` で書いた事後条件も `postcondition not satisfied` で失敗した。

- ガイドの機能一覧（`features.md`）で、浮動小数点は「Partially supported」とされている。
- vstd の f32 の比較の仕様（`vstd/std_specs/cmp.rs` 358〜416 行）は、`x < y` の結果 `o` について未解釈関数 `lt_ensures::<f32>(x, y, o)` が成り立つ、としか言わない。同じ箇所のコメントには「Rust の浮動小数点演算は決定的と保証されないので、`obeys_*_spec() == true` を仮定しない。代わりに、ユーザーが公理を与えるための未解釈関数を返す」とある。
- 公式例 `examples/float.rs` の冒頭には、「Verus deliberately omits axioms about floating point from vstd」とある。

仕様を付けた版はコメントアウトして残してある。`postcondition not satisfied` が 2 件出て失敗する。

```rust
pub fn clamp01(x: f32) -> (r: f32)
    ensures
        lt_ensures(x, 0.0f32, true) ==> r == 0.0f32,
        gt_ensures(x, 1.0f32, true) ==> r == 1.0f32,
        lt_ensures(x, 0.0f32, false) && gt_ensures(x, 1.0f32, false) ==> r == x,
```

現在のコードは仕様なしの `clamp01`（`verification results:: 1 verified, 0 errors`）。

#### Aeneas

**変換できない。** `aeneas` が `[Error] Improperly typed constant value`（`src/lib.rs` 2:7〜2:14、`x < 0.0` の部分）で終了する。エラーで終了しても本体が `sorry` の不完全な Lean ファイルが出力されるが、使えないので削除した。Aeneas が浮動小数点をサポートしていないことの根拠は 5.1 節に示す。

### 4.4 浮動小数点数の add（`04_add_f32`）

**関数と仕様:** `add_f32(a: f32, b: f32) -> f32` は `a + b` を返す。本来の仕様は次の 3 つ。

- 結果が NaN になるのは、どちらかが NaN か、符号の異なる無限大どうしを足したときに限る。
- 結果が ±∞ になる条件（入力に無限大があるか、有限な値どうしの和がオーバーフローするか）。
- 結果は、実数としての和を最も近い f32 に丸めた値（RNE）である。

#### Kani

**書けない。** NaN になる条件は書けるが、±∞ になる条件と丸めの仕様は書けない。

```rust
#[cfg(kani)]
#[kani::proof]
fn check_nan() {
    let a: f32 = kani::any();
    let b: f32 = kani::any();
    let opposite_infinities = a.is_infinite() && b.is_infinite() && a.is_sign_positive() != b.is_sign_positive();
    assert_eq!(add_f32(a, b).is_nan(), a.is_nan() || b.is_nan() || opposite_infinities);
}
```

```toml
[package.metadata.kani.flags]
no-overflow-checks = true
```

- **NaN になる条件は、必要十分条件として書けた。** すべての f32 の組について成り立つことを確かめた。
- **Kani は既定で、NaN を生む足し算を誤りとして扱う。** 既定のままだと、上のアサーションは成功するが、Kani の安全検査「NaN on addition」が失敗して `VERIFICATION:- FAILED` になる。この検査は、整数のオーバーフローと同じ「overflow checks」に含まれていて、`--no-overflow-checks` で外れる。この関数は NaN を返すことが正しい振る舞いなので、Kani 公式の設定方法である `Cargo.toml` の `[package.metadata.kani.flags]` で、このクレートだけ外した。
- **±∞ になる条件と丸めは書けない。** 有限な値どうしの和がオーバーフローするかどうか、また丸めの仕様は、実数の和を使わないと書けない。Kani の API（`~/.kani/kani-0.68.0/library/kani/src`）には実数の型がなく、ハーネスは普通の Rust の式で書く。f64 の和は丸められた値で実数の和ではないので、代わりには使えない。
- **丸めが起きることは反例で示せる。** 結合法則 `(a + b) + c == a + (b + c)` を主張するハーネス（コメントアウト済み）は失敗し、反例として `a = 1.5`、`b = -0.5`、`c ≈ 0.781249` が出た。途中の和がすべて有限であることを仮定しているので、オーバーフローではなく丸めによる不一致。
- 結果: `Complete - 1 successfully verified harnesses, 0 failures, 1 total.`

#### Creusot

**書けない。** 3 つの仕様のどれも書けなかった。書こうとした版は、理由とともにコメントアウトして残してある。現在のコードは仕様なしの `add_f32`（`Proved (verif/add_f32_rlib/add_f32.coma) ✔`）。

1. **NaN / ±∞ の条件:** Rust の `f32::is_finite` / `f32::is_nan` を仕様に使えない。
   - 仕様の中では `called program function core::f32::<impl f32>::is_finite in logic context` でコンパイルできない。creusot-std はこれらの関数に仕様を与えていない。
   - プログラムの中で呼ぶと、`calling external function is_finite with no contract will yield an impossible precondition` という警告が出て、検証条件が `false` になる。
2. **`f32::MAX` を使った条件:** 「`|a|, |b| ≤ f32::MAX / 2` なら和は有限」も書けない。
   - Creusot が定数を Why3 に書き出す処理（`why3/src/printer.rs` の `print_float`、1155〜1170 行）は、小数部のある値を正確な 16 進表記で出力する。一方、整数値の浮動小数点数は、f64 として最短で往復できる 10 進表記で出力する。
   - そのため `f32::MAX / 2`（正確な値は 170141173319264429905852091742258462720）が `170141173319264430000000000000000000000.0` と出力され、Float32 で正確に表せない値になる。Why3（`src/util/number.ml` 439〜507 行の `compute_float`）はこれを拒否し、why3find が `Fatal error: exception Invalid floating point literal` で止まる。
   - 標準ライブラリの定数 `f32::MAX` を直接参照すると、`does not have a "mir_for_ctfe"` という別の内部エラーになる。
3. **丸めの仕様:** 「結果は実数の和に最も近い f32」を書くには、f32 の実数値が要る。
   - creusot-std は f32 のビュー（`@`）を提供していないので、`Cannot take the view of f32` でコンパイルエラーになる。
   - 仕様の中では f32 の加算も使えない（`#[ensures(result == a + b)]` は `Cannot add f32 to f32 in logic`）。
4. **反例が出ない:** Creusot は証明の失敗を報告するだけで、反例を出さない。

#### Verus

**書けるが、証明できない。** 仕様の側には IEEE の演算と判定（`ieee_add`、`ieee_is_nan`、`ieee_is_infinite`）と、丸めなしの実数への変換（`as real`）があり、3 つの仕様はどれも書ける。仕様の中だけの事実（有限な 2 数の `ieee_add` は NaN でない、など）は `by (bit_vector)` で証明できる。しかし、実行コードの `a + b` の仕様は、未解釈関数 `add_ensures::<f32>(a, b, r)` が成り立つことだけ（`vstd/std_specs/ops.rs` 737〜761 行）で、仕様の `ieee_add` と結びついていない。`r == a.ieee_add(b)` という事後条件も `postcondition not satisfied` で失敗した。結びつけるには、公理を自分で仮定するしかない。仕様付きの版（有限な 2 数の和は NaN でない）はコメントアウトして残してあり、`postcondition not satisfied` で失敗する。現在のコードは仕様なしの `add_f32`（`verification results:: 1 verified, 0 errors`）。

#### Aeneas

**変換できない。** `aeneas` が `[Error] Invalid inputs for binop` で終了する（f32 の `+`）。

### 4.5 unsafe ポインタ（`05_raw_ptr`）

**関数と仕様:** `incr_on_heap(v: u64) -> u64` は、ヒープに置いた `v` を生ポインタ経由で 1 増やし、読み出してから解放する。事前条件は `v < u64::MAX`、事後条件は「結果は `v + 1`」。

#### Kani

```rust
pub fn incr_on_heap(v: u64) -> u64 {
    let p: *mut u64 = Box::into_raw(Box::new(v));
    unsafe {
        *p += 1;
        let r = *p;
        drop(Box::from_raw(p));
        r
    }
}
```

- 普通の unsafe コードがそのまま検証対象になる。生ポインタの参照外し、解放済みメモリへのアクセス、二重解放などは、CBMC のメモリモデルで自動的に検査される。
- ハーネスは `kani::assume(v < u64::MAX)` のもとで `incr_on_heap(v) == v + 1` を確かめる。
- 出力に `std::alloc::handle_alloc_error::rt_error.unsupported_construct` というチェックも出るが、メモリ確保に失敗したときだけ通る経路で、`Status: SUCCESS`（その経路には到達しない）なので結果に影響しない。
- 結果: `VERIFICATION:- SUCCESSFUL`

#### Creusot

```rust
use creusot_std::{ghost::perm::Perm, prelude::*};

#[requires(v@ < u64::MAX@)]
#[ensures(result@ == v@ + 1)]
pub fn incr_on_heap(v: u64) -> u64 {
    let (p, mut perm) = Perm::new(v);
    unsafe {
        *Perm::as_mut(p, perm.borrow_mut()) += 1;
        let r = *Perm::as_ref(p, perm.borrow());
        Perm::drop(p, perm);
        r
    }
}
```

- `Perm::new(v)` は、値を `Box` に入れ、生ポインタと、そのメモリへのアクセス権 `Ghost<Perm<*const u64>>` の組を返す。`Perm` はゴースト値で、実行時には消える。
- 読み書きの `Perm::as_ref` / `Perm::as_mut` は、「このポインタに対する権限であること」を事前条件に持つ。権限のないポインタの参照外しは、検証で弾かれる。
- 解放の `Perm::drop` は権限を消費するので、解放後に同じ権限で読むコードは書けない。
- 結果: `Proved (verif/raw_ptr_rlib/incr_on_heap.coma) ✔`

#### Verus

```rust
use vstd::simple_pptr::PPtr;

pub fn incr_on_heap(v: u64) -> (r: u64)
    requires
        v < u64::MAX,
    ensures
        r == v + 1,
{
    let (p, Tracked(mut perm)) = PPtr::<u64>::new(v);
    let x = p.read(Tracked(&perm));
    p.write(Tracked(&mut perm), x + 1);
    p.into_inner(Tracked(perm))
}
```

- `PPtr<V>` は vstd のポインタ型で、中身はアドレス。アクセス権は別の値 `PointsTo<V>` が持つ。`PointsTo` は `Tracked` に包まれた線形のゴースト値で、検証時には借用検査の対象になる。
- `read` / `write` は `perm.pptr() == self` を要求し、`into_inner` は値を取り出して解放し、`PointsTo` を消費する。
- 構造は Creusot の `Perm` とほぼ同じで、実行時の値とゴーストの権限を分けて持つ。違いは、ゴーストの受け渡しに `Tracked(...)` で包む記法を使う点と、`PPtr` が生ポインタではなくアドレスを包んだ型である点。
- 結果: `verification results:: 1 verified, 0 errors`

#### Aeneas

**変換できない。** `aeneas` が `[Error] Aeneas does not yet support dereferencing raw pointers.` で終了する（`src/interp/InterpPaths.ml` 197 行）。README の「Targeted Subset And Current Limitations」に、unsafe code と concurrency は、進行中の分離論理の作業で今後対応するとある。

### 4.6 ループ（`06_max`）

**関数と仕様:** `max(v: &[u32]) -> u32` は、スライスの最大値を返す。事前条件は「空でない」、事後条件は「すべての要素は結果以下」かつ「結果はどこかの要素と等しい」。

```rust
pub fn max(v: &[u32]) -> u32 {
    let mut m = v[0];
    let mut i = 1;
    while i < v.len() {
        if v[i] > m {
            m = v[i];
        }
        i += 1;
    }
    m
}
```

#### Kani

**書けない。** ループを展開できる長さまでしか調べられず、すべての長さについての性質は示せない。

```rust
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(6)]
fn check_max() {
    let arr: [u32; 5] = kani::any();
    let v = kani::slice::any_slice_of_array(&arr);
    kani::assume(!v.is_empty());
    let r = max(v);
    assert!(v.iter().all(|&x| x <= r));
    assert!(v.contains(&r));
}
```

- `#[kani::unwind(6)]` はループを最大 6 回展開する指定（反復 5 回と終了判定 1 回）。`any_slice_of_array` で、長さ 0〜5 の任意のスライスを網羅する。
- 長さ 10 の配列を調べるハーネス（コメントアウト済み）は、`Failed Checks: unwinding assertion loop 0` で失敗する。展開回数が足りないことを、Kani は黙らずに失敗として報告する。逆に言えば、展開回数を超える長さについては何も保証しない。
- 結果: `VERIFICATION:- SUCCESSFUL`

#### Creusot

```rust
#[requires(v@.len() > 0)]
#[ensures(forall<i> 0 <= i && i < v@.len() ==> v@[i] <= result)]
#[ensures(exists<i> 0 <= i && i < v@.len() && v@[i] == result)]
pub fn max(v: &[u32]) -> u32 {
    let mut m = v[0];
    let mut i = 1;
    #[invariant(1 <= i@ && i@ <= v@.len())]
    #[invariant(forall<j> 0 <= j && j < i@ ==> v@[j] <= m)]
    #[invariant(exists<j> 0 <= j && j < i@ && v@[j] == m)]
    while i < v.len() { ... }
    m
}
```

- ループ不変条件を書けば、長さに制限なく証明できる。`v@` はスライスを数学の列として見たもの。
- 結果: `Proved (verif/max_rlib/max.coma) ✔`

#### Verus

```rust
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> v[j] <= m,
            exists|j: int| 0 <= j < i && v[j] == m,
        decreases v.len() - i,
```

- 不変条件は Creusot と同じ。Verus は実行コードのループにも停止性を要求するので、`decreases` が要る。Creusot では、プログラム関数の停止性は `#[check(terminates)]` を付けたときだけ検査される。
- 結果: `verification results:: 2 verified, 0 errors`

#### Aeneas

事前条件「空でない」は `debug_assert!(!v.is_empty())` で書いた。ループは再帰関数に翻訳される。

```lean
def max_loop (v : Slice Std.U32) (m : Std.U32) (i : Std.Usize) : Result Std.U32 := do
  let i1 := Slice.len v
  if i < i1
  then
    let i2 ← Slice.index_usize v i
    let m1 ← if i2 > m then ok i2 else ok m
    let i3 ← i + 1#usize
    max_loop v m1 i3
  else ok m
partial_fixpoint

def max (v : Slice Std.U32) : Result Std.U32 := do
  let b ← core.slice.Slice.is_empty v
  massert (¬ b)
  let m ← Slice.index_usize v 0#usize
  max_loop v m 1#usize
```

```lean
def MaxPost (v : Slice U32) (r : U32) : Prop :=
  (∀ j < v.length, v.val[j]! ≤ r) ∧ ∃ j < v.length, v.val[j]! = r

@[step]
theorem max_loop_spec (v : Slice U32) (m : U32) (i : Usize)
    (h1 : i.val ≤ v.length)
    (h2 : ∀ j < i.val, v.val[j]! ≤ m) (h3 : ∃ j < i.val, v.val[j]! = m) :
    max_loop v m i ⦃ r => MaxPost v r ⦄ := by
  unfold max_loop
  step*
  · split <;> step*
    · agrind [getElem!_pos]
    · exact ⟨i.val, by agrind, by agrind [getElem!_pos]⟩
    · agrind [getElem!_pos]
  · unfold MaxPost
    split_conjs <;> agrind
termination_by v.length - i.val
decreasing_by all_goals scalar_decr_tac

theorem max_spec (v : Slice U32) (h : 0 < v.length) :
    MaxCrate.max v ⦃ r => MaxPost v r ⦄ := by
  unfold MaxCrate.max
  step*
  · agrind [getElem!_pos]
  · exact ⟨0, by agrind, by agrind [getElem!_pos]⟩
```

- 再帰関数の仕様では、ループ不変条件を定理の仮定に書き、`termination_by`（減少量）と `decreasing_by scalar_decr_tac` を付ける（Aeneas のドキュメントの書き方）。`step*` は再帰呼び出しにこの定理自身を使う。
- 事後条件は述語 `MaxPost` にまとめた。まとめないと、`step*` が事後条件の ∧ と ∃ を分解してしまい、`agrind` が存在の証明に失敗した。存在を示す添字は明示した。
- `getElem!_pos` は、`v.val[j]!`（範囲外なら既定値を返す添字）と、範囲内である証明付きの添字 `v.val[j]` を結び付ける補題。
- 関数名 `max` が Lean の `Max.max` と曖昧になるので、`MaxCrate.max` と完全修飾名で書いた。
- 結果: `Build completed successfully`

### 4.7 iter_mut（`07_clamp_all`）

**関数と仕様:** `clamp_all(v: &mut [u32], hi: u32)` は、`hi` を超える要素を `hi` に置き換える。事後条件は「長さは変わらず、各要素は `min(元の値, hi)` になる」。4 ツールとも `for x in v.iter_mut()` で書いた。

#### Kani

**書けない。** ループを展開できる長さまでしか調べられず、すべての長さについての性質は示せない。

```rust
#[cfg(kani)]
#[kani::proof]
#[kani::unwind(6)]
fn check_clamp_all() {
    let mut arr: [u32; 5] = kani::any();
    let orig = arr;
    let len: usize = kani::any();
    kani::assume(len <= 5);
    let hi: u32 = kani::any();
    clamp_all(&mut arr[..len], hi);
    for i in 0..5 {
        if i < len {
            assert!(arr[i] == orig[i].min(hi));
        } else {
            assert!(arr[i] == orig[i]);
        }
    }
}
```

- 長さ 0〜5 の任意のスライスについて、範囲内の要素は `min(元の値, hi)` になり、範囲外の要素は変わらないことを確かめる。
- 長さ 6 の配列のハーネス（コメントアウト済み）は、`Failed Checks: unwinding assertion loop 0` で失敗する。
- `iter_mut` も標準ライブラリの実装をそのまま展開して調べるので、イテレータ専用の仕様は要らない。
- 結果: `VERIFICATION:- SUCCESSFUL`

#### Creusot

```rust
#[ensures((^v)@.len() == v@.len())]
#[ensures(forall<i> 0 <= i && i < v@.len() ==> (^v)@[i] == if v@[i] > hi { hi } else { v@[i] })]
pub fn clamp_all(v: &mut [u32], hi: u32) {
    #[invariant(forall<i> 0 <= i && i < produced.len() ==>
        ^produced[i] == if *produced[i] > hi { hi } else { *produced[i] })]
    for x in v.iter_mut() {
        if *x > hi {
            *x = hi;
        }
    }
}
```

- `v` が `&mut` のとき、`*v`（`v@`）は関数開始時の値、`^v` は関数が終わったあとの最終値（prophecy）を表す。
- for ループには、Creusot がゴースト変数 `produced`（イテレータがこれまでに返した `&mut u32` の列）を用意する。`*produced[i]` は返された時点の値、`^produced[i]` はその参照の最終値。
- 不変条件は「これまでに返した各参照の最終値は、元の値を `hi` で頭打ちにした値」。creusot-std の `iter_mut` の仕様が、`produced` の各参照の最終値を `^v` の要素に結び付けるので、ループ後に `^v` についての事後条件が出てくる。
- 結果: `Proved (verif/clamp_all_rlib/clamp_all.coma) ✔`

#### Verus

```rust
pub fn clamp_all(v: &mut [u32], hi: u32)
    ensures
        final(v)@.len() == old(v)@.len(),
        forall|i: int| #![auto] 0 <= i < old(v)@.len() ==>
            final(v)@[i] == if old(v)@[i] > hi { hi } else { old(v)@[i] },
{
    for x in it: v.iter_mut()
        invariant
            forall|i: int| #![auto] 0 <= i < it.index() ==>
                *final(it.seq()[i]) == if *it.seq()[i] > hi { hi } else { *it.seq()[i] },
    { ... }
}
```

- このバージョンの Verus は、可変参照を prophecy で扱う。`old(v)` が開始時の値、`final(v)` が最終値で、Creusot の `*v` / `^v` に当たる。
- `for x in it: v.iter_mut()` で反復の状態に `it` という名前を付け、`it.index()`（反復回数）と `it.seq()[i]`（i 番目に返された参照）を不変条件で使う。考え方は Creusot と同じ。
- `#![auto]` は、量化子のトリガーを Verus の自動選択に任せる指定。付けないと、自動で選んだトリガーについての注意が出る（検証自体は通る）。
- 結果: `verification results:: 2 verified, 0 errors`

#### Aeneas

`&mut` は「新しい値を返す」関数に翻訳される。`clamp_all` は書き換えた後のスライスを返す関数になり、Creusot の `^v` に当たるのはこの戻り値。ループは、要素を書き戻す関数 `back` を組み立てながら進む再帰関数になる。

```lean
def clamp_all_loop (iter : core.slice.iter.IterMut Std.U32)
  (back : core.slice.iter.IterMut Std.U32 → core.slice.iter.IterMut Std.U32)
  (hi : Std.U32) : Result (core.slice.iter.IterMut Std.U32) := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (let im := next_back iter1 none
                back im)
  | some x =>
    if x > hi
    then clamp_all_loop iter1 (fun im => let im1 := next_back im (some hi)
                                         back im1) hi
    else clamp_all_loop iter1 (fun im => let im1 := next_back im o
                                         back im1) hi
partial_fixpoint

def clamp_all (v : Slice Std.U32) (hi : Std.U32) : Result (Slice Std.U32) := do
  let (iter, iter_mut_back) ← core.slice.Slice.iter_mut v
  let back ← clamp_all_loop iter (fun im => im) hi
  ok (iter_mut_back back)
```

```lean
def clamp (hi x : U32) : U32 := if x > hi then hi else x

def BackInv (a : Slice U32) (hi : U32) (i : Nat) (back : iter.IterMut U32 → iter.IterMut U32) :
    Prop :=
  ∀ it' : iter.IterMut U32, it'.slice.length = a.length →
    (back it').slice.length = a.length ∧
    (∀ j < i, (back it').slice.val[j]! = clamp hi a.val[j]!) ∧
    (∀ j, i ≤ j → j < a.length → (back it').slice.val[j]! = it'.slice.val[j]!)

theorem BackInv.step (a : Slice U32) (hi : U32) (i : Nat) (y : U32)
    (back : iter.IterMut U32 → iter.IterMut U32) (h1 : i < a.length)
    (h2 : y = clamp hi a.val[i]!) (h3 : BackInv a hi i back) :
    BackInv a hi (i + 1) (fun it' => back { it' with slice := it'.slice.setAtNat i y })

@[step]
theorem clamp_all_loop_spec (a : Slice U32) (hi : U32) (it : iter.IterMut U32)
    (back : iter.IterMut U32 → iter.IterMut U32)
    (h1 : it.slice = a) (h2 : it.i ≤ a.length) (h3 : BackInv a hi it.i back) :
    clamp_all_loop it back hi ⦃ r =>
      r.slice.length = a.length ∧ ∀ j < a.length, r.slice.val[j]! = clamp hi a.val[j]! ⦄

theorem clamp_all_spec (v : Slice U32) (hi : U32) :
    clamp_all v hi ⦃ r => r.length = v.length ∧ ∀ j < v.length, r.val[j]! = clamp hi v.val[j]! ⦄
```

（証明は `agrind` と `Slice.getElem!_Nat_setAtNat` で行う。全体は `aeneas/07_clamp_all/proofs/ClampAll/Properties.lean`。）

- `BackInv` は「`back` が、先頭 `i` 個に `clamp` した値を書き、残りはそのままにする」という不変条件。
- Aeneas のライブラリには、`for x in it { *x = g(*x) }` の形のループ用の定理 `IterMut.loop_updateBody.spec` があるが、既定の `loop` 結合子で翻訳した場合のもので、再帰関数には使えない。そこで、その定理の内部で使われている不変条件（非公開の `UpdateInv`）と同じ形の `BackInv` を定義し、1 要素進めても保たれることを補題 `BackInv.step` として証明した。
- 結果: `Build completed successfully`

### 4.8 ジェネリクス（`08_get_or`）

**関数と仕様:** `get_or<T: Copy>(v: &[T], i: usize, default: T) -> T` は、`i` が範囲内なら `v[i]` を、範囲外なら `default` を返す。仕様はすべての型 `T` について成り立つべきもの。

#### Kani

**書けない。** 汎用の関数そのものを検証できず、型ごと・長さを限ってしか調べられない。

```rust
#[cfg(kani)]
fn check_get_or<T: kani::Arbitrary + Copy + PartialEq>() {
    let arr: [T; 3] = kani::any();
    let v = kani::slice::any_slice_of_array(&arr);
    let i: usize = kani::any();
    let d: T = kani::any();
    let r = get_or(v, i, d);
    if i < v.len() {
        assert!(r == v[i]);
    } else {
        assert!(r == d);
    }
}

#[cfg(kani)]
#[kani::proof]
fn check_get_or_u8() {
    check_get_or::<u8>();
}

#[cfg(kani)]
#[kani::proof]
fn check_get_or_char() {
    check_get_or::<char>();
}
```

- `#[kani::proof]` をジェネリックな関数に付けると、`the '#[kani::proof]' attribute cannot be applied to generic functions` でコンパイルエラーになる（コメントアウトして残してある）。Kani は具体的な型に単相化したコードを調べるので、ハーネスは型ごとに書く。
- 調べたのは u8 と char で、長さ 0〜3 のスライスだけ。それ以外の型や長さについては何も言えない。
- 結果: `Complete - 2 successfully verified harnesses, 0 failures, 2 total.`

#### Creusot

```rust
#[ensures(i@ < v@.len() ==> result == v@[i@])]
#[ensures(i@ >= v@.len() ==> result == default)]
pub fn get_or<T: Copy>(v: &[T], i: usize, default: T) -> T
```

- 型パラメータ `T` のまま 1 回だけ検証され、すべての `T` について成り立つ。
- 結果: `Proved (verif/get_or_rlib/get_or.coma) ✔`

#### Verus

```rust
pub fn get_or<T: Copy>(v: &[T], i: usize, default: T) -> T
    returns
        (if i < v.len() { v[i as int] } else { default }),
```

- Creusot と同じく、すべての `T` について 1 回で検証される。仕様の中で添字を使うときは `int` にする（`v[i as int]`）。
- 結果: `verification results:: 1 verified, 0 errors`

#### Aeneas

```lean
def get_or {T : Type _} (coremarkerCopyInst : core.marker.Copy T) (v : Slice T)
  (i : Std.Usize) (default : T) : Result T := do
  let i1 := Slice.len v
  if i < i1
  then Slice.index_usize v i
  else ok default
```

```lean
theorem get_or_spec {T : Type} (inst : core.marker.Copy T) (v : Slice T)
    (i : Usize) (default : T) :
    get_or inst v i default ⦃ r => r = (v.val[i.val]?).getD default ⦄ := by
  unfold get_or
  step*
  · rw [List.getElem?_eq_getElem (by agrind)]
    simp_all
  · simp_all
```

- トレイト境界 `T: Copy` は、インスタンスを表す引数（`core.marker.Copy T`）に翻訳される。定理は任意の `T` について 1 つ書けばよい。
- 仕様の `v.val[i.val]?` は「範囲内なら `some v[i]`、範囲外なら `none`」で、`getD default` で範囲外のときに `default` になる。この書き方なら、`T` に追加の仮定は要らない。
- 結果: `Build completed successfully`

### 4.9 ジェネリクス + `==`（`09_contains`）

**関数と仕様:** 3 つの関数を用意した。

1. **`contains<T: PartialEq>(v: &[T], x: &T) -> bool`**: `v` に `x` と `==` が真になる要素があれば `true`。
   - 事後条件は「結果が `true` ⇔ `v` のどこかに、`x` との `==` が真になる要素がある」。その型自身の `==` を使って書くので、`==` がキーだけを比べる型（関係のないメタデータを無視する型など）もそのまま扱える。
   - 事前条件として要るのは、`==` が呼ぶたびに同じ結果を返し、失敗しないことだけ。`==` が値の等しさと一致する必要はない。
2. **`contains_vertex(v: &[Vertex], x: &Vertex) -> bool`**: 自作の型 `Vertex { x: i32, y: i32 }`（`==` は全フィールドの比較）で `contains` を呼ぶ。事後条件は「結果が `true` ⇔ フィールドがすべて等しい要素がある」。
3. **`contains_f32(v: &[f32], x: f32) -> bool`**: f32 では `NaN == NaN` が偽で、汎用の `contains` では配列中の NaN が見つからない。そこで NaN どうしも一致とみなす特殊処理を入れた。事後条件は「結果が `true` ⇔ `v[i] == x`（IEEE の比較）か、`v[i]` と `x` がともに NaN である要素がある」。

```rust
pub fn contains_f32(v: &[f32], x: f32) -> bool {
    let mut i = 0;
    while i < v.len() {
        if v[i] == x || (v[i] != v[i] && x != x) {
            return true;
        }
        i += 1;
    }
    false
}
```

#### Kani

**書けない。** 汎用の関数そのものを検証できず、型ごと・長さを限ってしか調べられない。

```rust
#[derive(PartialEq, Clone, Copy)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Vertex {
    pub x: i32,
    pub y: i32,
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(4)]
fn check_contains_vertex() {
    let arr: [Vertex; 3] = kani::any();
    let v = kani::slice::any_slice_of_array(&arr);
    let x: Vertex = kani::any();
    let expected = v.iter().any(|y| y.x == x.x && y.y == x.y);
    assert_eq!(contains_vertex(v, &x), expected);
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(4)]
fn check_contains_f32() {
    let arr: [f32; 3] = kani::any();
    let v = kani::slice::any_slice_of_array(&arr);
    let x: f32 = kani::any();
    let expected = v.iter().any(|&y| y == x || (y.is_nan() && x.is_nan()));
    assert_eq!(contains_f32(v, x), expected);
}
```

- Kani は具体的な型の `PartialEq` の実装（derive したものを含む）をそのまま実行してたどる。その代わり、汎用の `contains` そのものは検証できず、型ごとにハーネスを書く（4.8 節）。
- 調べたのは長さ 0〜3 のスライスだけ。f32 版は、NaN・±∞・±0 を含むすべての f32 について確かめた。
- 汎用の `contains` に f32 の配列を渡すハーネス（コメントアウト済み）は、配列中の NaN が見つからずに失敗する。
- 結果: `Complete - 2 successfully verified harnesses, 0 failures, 2 total.`

#### Creusot

**書けない。** 汎用の `contains` と自作の型の版は書けるが、`contains_f32` の仕様を書けない（下の「f32 版は書けない」）。

```rust
use creusot_std::{prelude::*, std::cmp::PartialEq};

#[ensures(result == exists<i> 0 <= i && i < v@.len() && v@[i].deep_model() == x.deep_model())]
pub fn contains<T: PartialEq + DeepModel>(v: &[T], x: &T) -> bool

#[derive(PartialEq)]
pub struct Vertex {
    pub x: i32,
    pub y: i32,
}

impl DeepModel for Vertex {
    type DeepModelTy = (i32, i32);

    #[logic(open)]
    fn deep_model(self) -> Self::DeepModelTy {
        (self.x, self.y)
    }
}

#[ensures(result == exists<i> 0 <= i && i < v@.len() && v@[i].x == x.x && v@[i].y == x.y)]
pub fn contains_vertex(v: &[Vertex], x: &Vertex) -> bool
```

- **`==` の表し方:** creusot-std は `PartialEq::eq` に `#[ensures(result == (self.deep_model() == rhs.deep_model()))]` という仕様を付けている（`creusot-std/src/std/cmp.rs`）。`==` は「deep model（比較用の論理上の値）が等しいときに限り真」として扱われ、`contains` の事後条件もこの deep model で書く。
  - deep model は型ごとに選べる。キーだけを比べる型なら、deep model をキーにすればよい。したがって、この仕様は値の等しさを要求していない。
  - 各型の `PartialEq` の実装がこの仕様を満たすことは、Creusot が実装ごとに検証する（`impl_PartialEq_for_Vertex/eq__refines.coma` が生成される）。
- **DeepModel:** `creusot-std/src/model.rs` のドキュメントコメントでは、「等価性・ハッシュ・順序などの仕様に使うモデルで、データ構造の中まで再帰的に計算されるもの」と説明されている。ガイド（`view.md`）には「explain DeepModel」という TODO が残っていて、まだ説明がない。ビュー `@` が浅いモデルなのに対し、`deep_model` は中身まで再帰的にたどる（`Vec<Box<u32>>` の `@` は `Seq<Box<u32>>`、`deep_model` は `Seq<Int>`）。
- **自作の型:** `#[derive(PartialEq)]` は creusot-std の derive（`use creusot_std::std::cmp::PartialEq;`）を使う。`DeepModel` は手で実装した。`#[derive(DeepModel)]` もあるが、通常の `cargo build` では何も生成しないので（`creusot-std-proc/src/dummy.rs` 116 行）、通常ビルドが `Vertex: DeepModel is not satisfied` で失敗する。
- **f32 版は書けない:** f32 には `DeepModel` がない。`NaN == NaN` が偽なので、「deep model が等しいときに限り真」を満たすモデルが存在しないためだ。また、特殊処理の仕様に要る `f32::is_nan` と IEEE の `==` は、どちらも仕様で使えない。仕様を付けた版は理由とともにコメントアウトして残してあり、`contains_f32` は仕様なしで置いてある。
- 結果: `Proved (5 files) ✔`

#### Verus

**書けない。** 汎用の `contains` と自作の型の版は書けるが、`contains_f32` の仕様を書けない（下の「f32 版は書けない」）。

```rust
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

pub fn contains<T: PartialEq>(v: &[T], x: &T) -> (r: bool)
    requires
        T::obeys_eq_spec(),
    ensures
        r == exists|i: int| 0 <= i < v.len() && v[i].eq_spec(x),
{
    let mut i = 0;
    while i < v.len()
        invariant
            T::obeys_eq_spec(),
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> !v[j].eq_spec(x),
        decreases v.len() - i,
    {
        if v[i] == *x {
            return true;
        }
        i += 1;
    }
    false
}

impl PartialEq for Vertex {
    fn eq(&self, other: &Vertex) -> (r: bool)
        ensures
            r == (self == other),
    {
        self.x == other.x && self.y == other.y
    }
}

// Vertex の == が eq_spec に従うことを vstd に伝える
impl vstd::std_specs::cmp::PartialEqSpecImpl for Vertex {
    open spec fn obeys_eq_spec() -> bool {
        true
    }

    open spec fn eq_spec(&self, other: &Vertex) -> bool {
        self == other
    }
}
```

- **`==` の表し方:** vstd は `PartialEq::eq` に次の仕様を付けている（`vstd/std_specs/cmp.rs`）。

  ```rust
  spec fn obeys_eq_spec() -> bool;
  spec fn eq_spec(&self, other: &Rhs) -> bool;
  fn eq(&self, other: &Rhs) -> (r: bool)
      ensures
          Self::obeys_eq_spec() ==> r == self.eq_spec(other);
  ```

  `eq_spec` は `==` の意味を表す仕様用の関数で、`obeys_eq_spec()` は「この型の `eq` が `eq_spec` に従うか」を表す。`contains` の事前条件は `T::obeys_eq_spec()` で、事後条件は `eq_spec` で書いた。`eq_spec` は型ごとに定めるので、キーだけを比べる型も扱える。
- **自作の型:** `PartialEqSpecImpl` で `obeys_eq_spec` と `eq_spec` を与え、`eq` の実装に事後条件を付けた（Verus のテスト `source/rust_verify_test/tests/eq_cmp.rs` と同じ形）。`contains_vertex` の事後条件は、`eq_spec`（構造体の等しさ）からフィールドの等しさとして導かれる。
- **f32 版は書けない:** vstd は f32 の `==` の結果を未解釈関数でしか表さない（4.3 節と同じ理由）。仕様を付けた版はコメントアウトして残してあり、`invariant not satisfied at end of loop body` で失敗する。
- 結果: `verification results:: 6 verified, 0 errors`

#### Aeneas

**書けない。** 汎用の `contains` と自作の型の版は書けるが、`contains_f32` を変換できない（下の「f32 版は変換できない」）。

トレイト境界 `T: PartialEq` は、インスタンスを表す引数（`core.cmp.PartialEq T T`）に翻訳され、`v[i] == *x` はその `eq` フィールドの呼び出しになる。derive した `Vertex` の実装も Lean に翻訳される。

```lean
def Vertex.Insts.CoreCmpPartialEqVertex.eq (self : Vertex) (other : Vertex) : Result Bool := do
  if self.x = other.x
  then ok (self.y = other.y)
  else ok false
```

```lean
theorem contains_spec {T : Type} (inst : core.cmp.PartialEq T T) (v : Slice T) (x : T)
    (h0 : ∀ y ∈ v.val, ∃ c, inst.eq y x = ok c) :
    contains inst v x ⦃ r => r = true ↔ ∃ y ∈ v.val, inst.eq y x = ok true ⦄ := by
  unfold contains
  step*
  simp

theorem vertex_eq_eq (a b : Vertex) :
    ∃ c, Vertex.Insts.CoreCmpPartialEqVertex.eq a b = ok c ∧ (c = true ↔ a = b) := by
  obtain ⟨ax, ay⟩ := a
  obtain ⟨bx, by_⟩ := b
  unfold Vertex.Insts.CoreCmpPartialEqVertex.eq
  split <;> simp_all

theorem contains_vertex_spec (v : Slice Vertex) (x : Vertex) :
    contains_vertex v x ⦃ r => r = true ↔ x ∈ v.val ⦄
```

（ループの仕様 `contains_loop_spec` と `contains_vertex_spec` の証明は `aeneas/09_contains/proofs/Contains/Properties.lean`。）

- **`contains`:** 事後条件は、その型自身の `eq` の結果で書いた。事前条件 `h0` は「`v` の要素と `x` の組で `eq` が失敗しない」。Lean の `eq` は `Result` を返すので、失敗しうる。`eq` が panic すれば `contains` も実際に失敗するので、これは動作に表れる条件で、呼び出し側の定理が `contains` の振る舞いに頼る限り、示さないと証明できない。
- **`contains_vertex`:** `vertex_eq_eq` で `Vertex` の `eq` が失敗せず、全フィールドの等しさと一致することを示し、`contains_spec` から仮定のない定理として証明した。
- **f32 版は変換できない。** `contains_f32` を含めたまま変換すると、`aeneas` はエラーも警告も出さずに終了するが、生成された Lean は未定義の型 `F32` を参照していて、`lake build` が `failed to synthesize instance of type class BEq F32` で失敗する。float を含むコードがエラーなしで壊れた Lean になる症状は、Aeneas の Issue #828 にも報告されている。生成ファイルは 1 つなので、このままでは他の関数の証明もビルドできない。Charon の公式オプション `--exclude=crate::contains_f32` で、この関数だけを変換対象から外した（Rust のコードには残してある）。
- 結果: `Build completed successfully`

### 4.10 並行処理: Counting to 2（`10_count_to_two`）

**関数と仕様:** `count_to_two() -> u32` は、共有の `AtomicU32` に 2 つのスレッドがそれぞれ `fetch_add(1)` を行い、両方を `join().unwrap()` してから値を読む。事後条件は「結果は 2」。

```rust
pub fn count_to_two() -> u32 {
    let counter = Arc::new(AtomicU32::new(0));
    let c1 = Arc::clone(&counter);
    let t1 = thread::spawn(move || increment(&c1));
    let c2 = Arc::clone(&counter);
    let t2 = thread::spawn(move || increment(&c2));
    t1.join().unwrap();
    t2.join().unwrap();
    counter.load(Ordering::SeqCst)
}
```

演繹的検証では、それぞれのスレッドから見えるのは「自分が 1 足した」ことだけで、「相手も 1 足した」ことは分からない。そのため、全体で起きたことを記録するゴーストの状態を共有し、atomic 操作と同時に更新する仕組みが要る。

#### Kani

**検証できない。** `count_to_two` を呼ぶハーネス（コメントアウト済み）は、検証の前に Kani のコンパイラ自体が内部エラーで止まる。

```
thread 'rustc' panicked at kani-compiler/src/intrinsics.rs:243:17:
Kani unexpectedly panicked during compilation.
error: internal compiler error: Kani unexpectedly panicked ...
```

切り分けると、atomic 型だけなら問題なく、`thread::spawn` に到達すると落ちる。Kani はスレッドによる並行実行をサポートしておらず、スレッドの実行順の組み合わせを探索する仕組みもない。

#### Creusot

creusot-std の公式例 `examples/parallel_add/sc.rs`（2 スレッドが 2 ずつ足して 4 になる例）を、`AtomicU32` と `fetch_add(1)` に置き換えて使った。コードは `creusot/10_count_to_two/src/lib.rs`。

主な構成要素は次のとおり。

1. **`creusot_std::std::sync::atomic_sc::AtomicU32`:** 標準の `AtomicU32` の代わりに使う、Creusot 独自のラッパー。`AtomicU32::new(0)` は、atomic 本体とその値の所有権 `Ghost<Perm<AtomicU32>>` を返す。
   - `atomic_sc` は creusot-std の `sc-drf` フィーチャーを有効にしたときだけ使える（3.6 節）。
   - SC-DRF は「データ競合のないプログラムで、atomic 操作をすべて SeqCst で行えば、実行は逐次一貫になる」という仮定。メモリオーダーは型で指定する（`Committer<_, _, SeqCst, SeqCst>`）。
   - 既定の `std::sync::atomic` は弱いメモリモデル版で、`Relaxed` や `Acquire` / `Release` も扱えるが、値をタイムスタンプ付きの書き込み履歴として扱う追加のゴーストが必要になる（公式例 `examples/parallel_add/rlx.rs`）。
2. **`Authority` / `Fragment`:** スレッドごとに「加算済みか」を表すリソース（`Option<Excl<bool>>`）。権威側を共有の不変条件の中に置き、断片側を各スレッドが持つ。`Excl` は排他的なリソース代数で、両者は常に同じ値に保たれるので、スレッドは自分の断片を通してしか自分のフラグを立てられない。
3. **`Protocol`:** `CounterInv` に `Perm<AtomicU32>` と 2 つの `Authority` をまとめ、`protocol()` で「atomic の値 = 加算済みのスレッド数」と定める。
4. **`AtomicInvariantSC`:** `CounterInv` を、スレッド間で共有する不変条件として包む。`declare_namespace!` で宣言した名前空間を付ける。
5. **`Tokens`:** 不変条件を開くための権利。名前空間ごとに 1 つあり、同じ不変条件を入れ子で 2 回開くことを防ぐ。
6. **`fetch_add` のゴースト引数:** `fetch_add` に渡すゴーストのクロージャは、atomic の更新の瞬間に実行されるものとして扱われる。その中で不変条件を開き、`Committer` で `Perm` の値を進め、同時に自分のフラグを立てる。
7. **`thread::scope` / `join_unwrap`:** 仕様付きのラッパー。`join().unwrap()` の代わりに `join_unwrap()` を使う。
8. **最後の ghost ブロック:** 不変条件を解体し、`frag_lemma` で「手元の `Fragment` が `Excl(true)` なので `Authority` も `Excl(true)`」を導いて、値が 2 であることを得る。

事後条件は `#[ensures(result@ == 2)]`。結果: `Proved (verif/count_to_two_rlib/count_to_two.coma) ✔`

#### Verus

Verus の公式チュートリアルの `examples/state_machines/tutorial/counting_to_2.rs` をほぼそのまま使った。コードは `verus/10_count_to_two/src/lib.rs`。

主な構成要素は次のとおり。

1. **`tokenized_state_machine!`:** 並行プロトコルを状態機械として定義する。フィールドは `counter`（論理上のカウンタ値）、`inc_a` / `inc_b`（各スレッドが加算済みか）の 3 つ。
   - `#[sharding(variable)]` を付けたフィールドは、別々のスレッドが持てるトークンに分割される。
   - `transition!` で遷移（`tr_inc_a`: 「`inc_a` が false なら `counter` を 1 増やし `inc_a` を true にする」）、`property!` で導ける事実（`finalize`: 「`inc_a` と `inc_b` が両方 true なら `counter == 2`」）を定める。
   - `#[invariant]` で「`counter` = 加算済みのスレッド数」と定め、各遷移がこれを保つことを Verus に証明させる。
2. **`vstd::atomic_ghost::AtomicU32`:** atomic の値と一緒にゴーストのトークンを保持する。`struct_with_invariants!` で「atomic の値とトークンの値が等しい」を不変条件にする。
3. **`atomic_with_ghost!`:** `fetch_add` と同時にゴーストのブロックを実行し、状態機械を遷移させる。
4. **`vstd::thread::spawn`:** クロージャに `ensures` を付け、「スレッドが終わると true になったトークンを返す」を仕様にする。
5. **最後の `load`:** 両方のトークンが true であることから `counter == 2` を導く。

**書けない。** 事後条件は「`join` が成功すれば 2」までしか書けない。vstd の `JoinHandle::join` の仕様（`vstd/thread.rs`）は次のとおりで、`Err` の場合は何も保証しない。

```rust
pub fn join(self) -> (r_result: Result<Ret, ()>)
    ensures
        match r_result {
            Result::Ok(r) => self.predicate(r),
            Result::Err(_) => true,
        },
```

`join` が `Ok` を返すことは示せないので、`join().unwrap()` を書くと `unwrap` の事前条件を満たせない。公式チュートリアルも、`Err` のときは `return` している。このリポジトリでは戻り値を `Result<u32, ()>` にし、事後条件を `r matches Ok(n) ==> n == 2` とした。元の関数の仕様「結果は 2」は書けない。

結果: `verification results:: 6 verified, 0 errors`

#### Aeneas

**証明できない。** `aeneas` は終了コード 0 で変換を終えるが、次のとおり、性質を述べる材料がない。

- `thread::spawn`、`JoinHandle::join`、`Arc::new` / `clone` / `deref`、`AtomicU32::new` / `fetch_add` / `load` は、中身のない axiom として `FunsExternal_Template.lean` に列挙されるだけ。
- `fetch_add` は `Atomic U32 → U32 → Ordering → Result U32` という型で、更新後の atomic を返さない。共有カウンタへの書き込みは、翻訳後のコードのどこにも現れない。
- README の「Targeted Subset And Current Limitations」で、並行処理は unsafe と並んで、分離論理の作業で今後対応する項目に挙がっている。

Lean のプロジェクトは作らず、生成されたファイルだけを `proofs/` に残した。

#### Creusot と Verus の対応

両者は同じ考え方（Iris 系の分離論理）を別の語彙で表している。

| 役割 | Creusot | Verus |
|---|---|---|
| 「誰が何をしたか」を表すゴーストの状態 | `Authority` / `Fragment`（リソース代数 `Excl`） | 状態機械のフィールドから分割したトークン |
| 共有する不変条件 | `AtomicInvariantSC` と `Protocol` | 状態機械の `#[invariant]` と atomic の `invariant on` |
| atomic 操作と同時のゴーストの更新 | `fetch_add` のゴーストのクロージャと `Committer` | `atomic_with_ghost!` |
| 不変条件の二重オープンの防止 | 名前空間と `Tokens` | 不変条件の名前空間（`atomic_with_ghost!` が管理） |
| 結論を導く | `frag_lemma` | `property!` の `finalize` |

### 4.11 証明の誘導（`11_count_eq`）

**関数と仕様:** `count_eq(v: &[u32], x: u32) -> usize` は、`v` の中の `x` の個数を返す。事後条件は「結果は `count(v, x)`」。`count` は仕様用の関数で、列の先頭から再帰的に定義する。

```rust
pub fn count_eq(v: &[u32], x: u32) -> usize {
    let mut c = 0;
    let mut i = 0;
    while i < v.len() {
        if v[i] == x {
            c += 1;
        }
        i += 1;
    }
    c
}
```

この題材では、ソルバーが単独では証明を通せず、補題や中間の主張で誘導する必要がある。

- ループ不変条件 `c == count(v[0..i], x)` を保つには、「列の末尾に要素を 1 つ足すと、`count` はその要素の分だけ増える」という性質が要る。定義（先頭から分解する）とは逆向きの主張なので、列の長さについての帰納法でしか示せない。SMT ソルバーは帰納法を自動では行わない。
- さらに、`v[0..i+1]` と「`v[0..i]` の末尾に `v[i]` を足した列」が等しいという外延的な等しさも、ソルバーは自分では使わない。

#### Kani

**証明の誘導はできない。** Kani は有界モデル検査で、展開した範囲を網羅的に調べる。範囲内なら誘導なしで決着し、範囲外は扱えない。補題や中間の主張で証明を通すという作業そのものがない。

比較のため、長さ 0〜5 の任意のスライスについて、結果が `v.iter().filter(|&&y| y == x).count()` と一致することを確かめるハーネスを置いた（`VERIFICATION:- SUCCESSFUL`）。長さ 6 以上については何も言えない。

#### Creusot

```rust
#[logic(open)]
#[variant(s.len())]
pub fn count(s: Seq<u32>, x: u32) -> Int {
    if s.len() == 0 { 0 } else { (if s[0] == x { 1 } else { 0 }) + count(s.tail(), x) }
}

#[logic]
#[variant(s.len())]
#[ensures(count(s.push_back(y), x) == count(s, x) + if y == x { 1 } else { 0 })]
pub fn lemma_count_push_back(s: Seq<u32>, y: u32, x: u32) {
    if s.len() > 0 {
        // 列の等しさはソルバーが自分では導かないので明示する
        proof_assert!(s.push_back(y).tail().ext_eq(s.tail().push_back(y)));
        // 再帰呼び出しが帰納法の仮定にあたる
        lemma_count_push_back(s.tail(), y, x)
    }
}

#[ensures(result@ == count(v@, x))]
pub fn count_eq(v: &[u32], x: u32) -> usize {
    let mut c = 0;
    let mut i = 0;
    #[invariant(i@ <= v@.len())]
    #[invariant(c@ <= i@)]
    #[invariant(c@ == count(v@.subsequence(0, i@), x))]
    while i < v.len() {
        // 列の等しさはソルバーが自分では導かないので明示する
        proof_assert!(v@.subsequence(0, i@ + 1).ext_eq(v@.subsequence(0, i@).push_back(v@[i@])));
        // 補題を取り込む
        snapshot!(lemma_count_push_back(v@.subsequence(0, i@), v@[i@], x));
        if v[i] == x {
            c += 1;
        }
        i += 1;
    }
    c
}
```

- **補題:** 戻り値 `()` の論理関数として書き、`#[ensures]` が主張になる。本体の再帰呼び出しが帰納法の仮定に当たる（ガイド `logic_functions/lemma_law.md`）。再帰には `#[variant]`（減少量）が要る。
- **`proof_assert!`:** その時点で成り立つ主張をプルーバに示させ、以降の証明で使えるようにする（ガイド `basic_concepts/proof_assert.md`）。
- **`snapshot!(lemma(...))`:** プログラムの中で補題を適用する。0.14.0 の変更履歴に「Snapshots now assert pre- and postconditions of logic functions calls. This enables "applying" lemmas inside programs.」とある。
- **`ext_eq`:** 列の外延的な等しさ。

補助を 1 つずつ外した結果（毎回 why3find のキャッシュを消して実行）:

| 外したもの | 結果 |
|---|---|
| 補題内の `proof_assert!(...ext_eq...)` | `Goal Coma.vc_lemma_count_push_back: ✘ (2/3)` |
| 補題内の再帰呼び出し（帰納法の仮定） | `Goal Coma.vc_lemma_count_push_back: ✘ (2/3)` |
| ループ内の `proof_assert!(...ext_eq...)` | `Goal Coma.vc_count_eq: ✘ (11/12)` |
| ループ内の `snapshot!(lemma_...)` | `Goal Coma.vc_count_eq: ✘ (12/13)` |
| なし | `Proved (3 files) ✔` |

#### Verus

```rust
pub open spec fn count(s: Seq<u32>, x: u32) -> nat
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { (if s[0] == x { 1nat } else { 0nat }) + count(s.drop_first(), x) }
}

pub proof fn lemma_count_push(s: Seq<u32>, y: u32, x: u32)
    ensures
        count(s.push(y), x) == count(s, x) + (if y == x { 1nat } else { 0nat }),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.push(y).drop_first() =~= s);
    } else {
        assert(s.push(y).drop_first() =~= s.drop_first().push(y));
        lemma_count_push(s.drop_first(), y, x);
    }
}

pub fn count_eq(v: &[u32], x: u32) -> (c: usize)
    ensures
        c == count(v@, x),
{
    let mut c: usize = 0;
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            c <= i,
            c == count(v@.subrange(0, i as int), x),
        decreases v.len() - i,
    {
        assert(v@.subrange(0, i + 1) =~= v@.subrange(0, i as int).push(v[i as int]));
        proof {
            lemma_count_push(v@.subrange(0, i as int), v[i as int], x);
        }
        if v[i] == x {
            c += 1;
        }
        i += 1;
    }
    assert(v@.subrange(0, v.len() as int) =~= v@);
    c
}
```

- **補題:** `proof fn` として書き、`decreases` で帰納法の正しさ（停止性）を示す。実行コードからは `proof { ... }` の中で呼ぶ。
- **`assert(a =~= b)`:** 列の外延的な等しさをソルバーに示させる（ガイド `extensional_equality.md`）。

補助を 1 つずつ外した結果:

| 外したもの | 結果 |
|---|---|
| 補題内の `assert(... =~= s.drop_first().push(y))` | `postcondition not satisfied`（補題） |
| 補題内の再帰呼び出し | `postcondition not satisfied`（補題） |
| ループ内の `assert(... =~= ...push(v[i]))` | `invariant not satisfied at end of loop body` |
| ループ内の `lemma_count_push(...)` | `invariant not satisfied at end of loop body` |
| ループ後の `assert(v@.subrange(0, len) =~= v@)` | `postcondition not satisfied` |
| なし | `verification results:: 4 verified, 0 errors` |

必要な誘導の種類（帰納法の補題、補題の適用、列の外延的な等しさ）は Creusot と同じだった。Verus ではループ後の `v[0..len] == v` も明示が必要だった。

#### Aeneas

```lean
def count (x : U32) : List U32 → Nat
  | [] => 0
  | y :: ys => (if y = x then 1 else 0) + count x ys

theorem count_append (x y : U32) (l : List U32) :
    count x (l ++ [y]) = count x l + (if y = x then 1 else 0) := by
  induction l <;> agrind [count]

@[step]
theorem count_eq_loop_spec (v : Slice U32) (x : U32) (c i : Usize)
    (h1 : i.val ≤ v.length) (h2 : c.val ≤ i.val) (h3 : c.val = count x (v.val.take i.val)) :
    count_eq_loop v x c i ⦃ r => r.val = count x v.val ⦄ := by
  unfold count_eq_loop
  step*
  · split <;> step* <;> agrind [count_append, List.take_succ_eq_append_getElem]
  · agrind [List.take_of_length_le]
termination_by v.length - i.val
decreasing_by all_goals scalar_decr_tac

theorem count_eq_spec (v : Slice U32) (x : U32) :
    count_eq v x ⦃ r => r.val = count x v.val ⦄ := by
  unfold count_eq
  step*
  agrind [count, List.take_zero]
```

- ループの各回では、`take (i + 1) = take i ++ [v[i]]`（`List.take_succ_eq_append_getElem`）と補題 `count_append` で、数え上げを 1 段進める。
- `agrind` も、この題材で要る補題と帰納法を自分では見つけない。次の部分を外すと失敗した。

  | 外したもの | 結果 |
  |---|---|
  | `count_append` を `agrind` に渡さない | `agrind failed` |
  | `List.take_succ_eq_append_getElem` を渡さない | `agrind failed` |
  | 補題を帰納法なし（`agrind [count]`）で証明する | `agrind failed` |

- Lean には SMT ソルバーがなく、証明のすべての段階を tactic で書く。そのうえで、補題と帰納法が要る点は Creusot・Verus と同じ。
- 結果: `Build completed successfully`

### 4.12 分割して畳み込む関数（`12_fold_halves`）

**関数と仕様:** スライスを半分に分け、それぞれを畳み込んだ結果を演算で結合する関数 `fold_halves` を、トレイト `Monoid` について汎用に書く。rayon の `reduce` などの並列の畳み込みと同じ形で、rayon の `reduce` のドキュメントも、演算が結合的であることを求めている。

```rust
pub trait Monoid: Copy {
    fn id() -> Self;
    fn op(a: Self, b: Self) -> Self;
}

pub fn fold<T: Monoid>(v: &[T]) -> T {
    let mut acc = T::id();
    let mut i = 0;
    while i < v.len() {
        acc = T::op(acc, v[i]);
        i += 1;
    }
    acc
}

pub fn fold_halves<T: Monoid>(v: &[T]) -> T {
    let (left, right) = v.split_at(v.len() / 2);
    T::op(fold(left), fold(right))
}
```

- **`Monoid`:** 単位元 `id` と演算 `op` を与えるトレイト。
- **`fold`:** 先頭から順に畳み込む。事後条件は「結果は `v` の畳み込み `fold_spec(v)`」。`fold_spec` は仕様用の関数で、`fold_spec([]) = id`、`fold_spec(s ++ [x]) = op(fold_spec(s), x)` と定義する。
- **`fold_halves`:** 事前条件は「`T` の `op` が結合的で、`id` が左右の単位元である」（モノイドの法則）。事後条件は「結果は `fold_spec(v)`」。結合律がなければ、分割した結果は順に畳み込んだ結果と一致しない。事前条件を満たさない型で `fold_halves` を呼ぶ関数は、検証で弾かれなければならない。
- **インスタンス:** 法則を満たす `Max`（最大値、単位元 0）と、満たさない `Diff`（差の絶対値、単位元 0）を用意した。`Diff` は単位元の法則は満たすが、結合律を満たさない（`(5, 3, 1)` で `op(op(5, 3), 1) = 1`、`op(5, op(3, 1)) = 3`）。`max_halves` と `diff_halves` は、それぞれで `fold_halves` を呼ぶ。

Creusot・Verus では、この事前条件を、トレイトに置いた法則として書いた。法則は実装する型ごとに証明させるので、事前条件を満たさない型はそもそも `Monoid` を実装できず、`fold_halves` を呼べない。そのため、Creusot・Verus 版の Rust のコードは Kani・Aeneas 版と異なる。

#### Kani

**書けない。** 汎用の `fold_halves` そのものを検証できない（4.8 節）。また、安定した機能では事前条件を関数に付けて呼び出し側に課せないので（4.2 節）、法則を満たさない `Diff` で呼ぶ `diff_halves` も拒否されない。

```rust
#[derive(Clone, Copy)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct Max(pub u32);

#[cfg(kani)]
#[kani::proof]
fn check_max_laws() {
    let a: Max = kani::any();
    let b: Max = kani::any();
    let c: Max = kani::any();
    assert_eq!(Max::op(Max::op(a, b), c).0, Max::op(a, Max::op(b, c)).0);
    assert_eq!(Max::op(Max::id(), a).0, a.0);
    assert_eq!(Max::op(a, Max::id()).0, a.0);
}

#[cfg(kani)]
#[kani::proof]
#[kani::unwind(5)]
fn check_max_halves() {
    let arr: [Max; 4] = kani::any();
    let v = kani::slice::any_slice_of_array(&arr);
    assert_eq!(max_halves(v).0, fold(v).0);
}
```

- できるのは、型ごとにハーネスを書いて確かめることだけ。`Max` の法則はすべての u32 の組について確かめた。`Diff` の結合律のハーネス（コメントアウト済み）は `assertion failed` で失敗するが、これはハーネスを書いた型だけの話で、`Diff` の実装が拒否されるわけではない。
- 汎用の `fold_halves` そのものは検証できず（4.8 節）、`max_halves` は長さ 0〜4 のスライスだけを調べた。
- 結果: `Complete - 2 successfully verified harnesses, 0 failures, 2 total.`

#### Creusot

```rust
pub trait Monoid: Sized + Copy {
    #[logic]
    fn id_spec() -> Self;

    #[logic]
    fn op_spec(a: Self, b: Self) -> Self;

    #[logic(law)]
    #[ensures(Self::op_spec(Self::op_spec(a, b), c) == Self::op_spec(a, Self::op_spec(b, c)))]
    fn assoc(a: Self, b: Self, c: Self);

    #[logic(law)]
    #[ensures(Self::op_spec(Self::id_spec(), a) == a)]
    #[ensures(Self::op_spec(a, Self::id_spec()) == a)]
    fn identity(a: Self);

    #[ensures(result == Self::id_spec())]
    fn id() -> Self;

    #[ensures(result == Self::op_spec(a, b))]
    fn op(a: Self, b: Self) -> Self;
}

#[ensures(result == fold_spec(v@))]
pub fn fold_halves<T: Monoid>(v: &[T]) -> T {
    let (left, right) = v.split_at(v.len() / 2);
    proof_assert!(v@.ext_eq(left@.concat(right@)));
    snapshot!(lemma_fold_concat(left@, right@));
    T::op(fold(left), fold(right))
}
```

- **法則:** ガイドの `logic_functions/lemma_law.md` によると、トレイトの論理関数に付けた事後条件は、実装する側が証明しなければならない。`#[logic(law)]` を付けると、同じトレイトの関数を使うときに、その法則が自動で証明の文脈に入る。
- **`fold_halves` の証明:** 補題 `lemma_fold_concat`（`fold_spec(s ++ t) == op(fold_spec(s), fold_spec(t))`、`t` の長さについての帰納法）を、`v` が `left ++ right` に等しいことと合わせて使う。補題の中では、法則が自動で使われる。
- **`Max`:** 実装の側で、法則の事後条件を本体が空の論理関数として書き、ソルバーが示した。
- **`Diff`:** 実装すると `Goal Coma.vc_assoc_Diff: ✘` で拒否される。理由とともにコメントアウトした。
- 結果: `Proved (14 files) ✔`

#### Verus

```rust
pub trait Monoid: Sized + Copy {
    spec fn id_spec() -> Self;

    spec fn op_spec(a: Self, b: Self) -> Self;

    proof fn lemma_assoc(a: Self, b: Self, c: Self)
        ensures
            Self::op_spec(Self::op_spec(a, b), c) == Self::op_spec(a, Self::op_spec(b, c)),
    ;

    proof fn lemma_id(a: Self)
        ensures
            Self::op_spec(Self::id_spec(), a) == a,
            Self::op_spec(a, Self::id_spec()) == a,
    ;

    fn id() -> (r: Self)
        ensures
            r == Self::id_spec(),
    ;

    fn op(a: Self, b: Self) -> (r: Self)
        ensures
            r == Self::op_spec(a, b),
    ;
}

pub fn fold_halves<T: Monoid>(v: &[T]) -> (r: T)
    ensures
        r == fold_spec(v@),
{
    let (left, right) = v.split_at(v.len() / 2);
    proof {
        assert(v@ =~= left@ + right@);
        lemma_fold_concat(left@, right@);
    }
    T::op(fold(left), fold(right))
}
```

- **法則:** ガイドの `traits.md`（「Spec and proof functions」）によると、トレイトに `proof fn` を宣言すると、実装する側はその本体で事後条件を証明しなければならない。法則は `lemma_assoc` と `lemma_id` として置いた。
- **`fold_halves` の証明:** Creusot と同じ補題 `lemma_fold_concat` を帰納法で示す。Verus では法則が自動では使われないので、補題の中で `T::lemma_id` と `T::lemma_assoc` を明示的に呼ぶ。
- **`Max`:** `proof fn` の本体は空のままで、ソルバーが示した。
- **`Diff`:** 実装すると、`lemma_assoc` が `postcondition not satisfied` で拒否される。理由とともにコメントアウトした。
- 結果: `verification results:: 11 verified, 0 errors`

#### Aeneas

**書けない。** `fold_halves` の事前条件（`T` の `op` が結合的で、`id` が単位元）を、呼び出し側に課す方法がない。

- **`assert!` で書けない。** Aeneas で事前条件を呼び出し側に課す方法は、事前条件を Rust の `assert!` / `debug_assert!` で書き、`massert` に翻訳させることである（5.2.2 節）。この事前条件は、それでは書けない。
  - `T: Monoid` の値どうしは、Rust で比べられない。`fold_halves` の先頭に、`v` の要素の組について結合律を確かめる `debug_assert!` を書くと、`error[E0369]: binary operation == cannot be applied to type T` でコンパイルできなかった（確かめたあと元に戻した）。
  - `T: PartialEq` を境界に足して比べられるようにしても、汎用の `==` が値の等しさを表すとは限らない（4.9 節）。
  - 結合律は `T` のすべての値の組についての条件で、汎用の型 `T` の値を Rust で数え上げる方法はない。`v` の要素の組だけを調べても、畳み込みの途中の値（`op` の結果）についての結合律は確かめられない。
- **トレイトにも書けない。** Lean に翻訳された `Monoid` は、`id` と `op` だけを持つ構造体で、法則を持たせる場所がない。Verus・Creusot の方法は使えない。

  ```lean
  structure Monoid (Self : Type _) where
    coremarkerCopyInst : core.marker.Copy Self
    id : Result Self
    op : Self → Self → Result Self
  ```

- **定理の仮定にはできるが、呼び出し側に課されない。** 法則を `fold_halves` の定理の仮定にすれば、定理は証明できる。`op` と `id` が純粋な関数 `f` と値 `e` で表せることも仮定に含める。

  ```lean
  theorem fold_halves_spec {T : Type} (inst : FoldHalves.Monoid T) (f : T → T → T) (e : T)
      (hop : ∀ a b, inst.op a b ⦃ r => r = f a b ⦄) (hid : inst.id ⦃ r => r = e ⦄)
      (hassoc : ∀ a b c, f (f a b) c = f a (f b c))
      (hidr : ∀ a, f a e = a) (v : Slice T) :
      fold_halves inst v ⦃ r => r = List.foldl f e v.val ⦄ := by
    unfold fold_halves
    step*
    rw [r_post, t_post, t1_post, left_post2, left_post3, ← foldl_assoc f hassoc, hidr,
      ← List.foldl_append, List.take_append_drop]

  def maxOp (a b : Max) : Max := if a ≥ b then a else b

  theorem max_halves_spec (v : Slice Max) :
      max_halves v ⦃ r => r = List.foldl maxOp 0#u32 v.val ⦄
  ```

  （`fold` のループの仕様、補題 `foldl_assoc`、`max_halves_spec` の証明は `aeneas/12_fold_halves/proofs/FoldHalves/Properties.lean`。）

  - しかし、この仮定は `fold_halves` を呼ぶ側に強制されない（5.2.2 節）。`fold_halves` には定義があるので、呼び出し側の証明で定義を展開すれば、定理を使わずに済む。実際、`Diff` で呼ぶ `diff_halves` について、`diff_halves v ⦃ _ => True ⦄`（失敗しない）という定理は証明できた（確かめたあと削除した）。
  - `Diff` について `fold_halves_spec` の形の定理を証明しようとすると、仮定 `hassoc`（結合律）が `agrind failed` で示せない（コメントアウト済み）。ただし、それは誰かがその定理を書いた場合だけで、`diff_halves` が検証で弾かれたことにはならない。
  - 証明に使うのは結合律と右単位元だけなので、仮定はこの 2 つにした（左単位元を仮定に入れると、未使用の変数として警告が出る）。`max_halves_spec` は、仮定を `Max` について示して証明した。
- `Properties.lean` のビルドは通る（`Build completed successfully`）が、`fold_halves` の事前条件を呼び出し側に課せていないので、この題材は書けていない。

### 4.13 外部ライブラリを信用する（`13_par_sum`）

**関数と仕様:** 外部のライブラリ（rayon）の関数の本体は検証せず、その仕様を宣言して信用し、それを前提にした自分の関数を検証する。確かめるのは、次の 2 点である。

1. 信用する仕様（事前条件と事後条件）を宣言できるか。
2. 信用した仕様の事前条件を満たさない呼び出しが、検証で弾かれるか。

```rust
pub trait Monoid: Copy + Send + Sync {
    fn id() -> Self;
    fn op(a: Self, b: Self) -> Self;
}

pub fn par_sum<T: Monoid>(v: &[T]) -> T {
    v.par_iter().copied().reduce(T::id, T::op)
}

impl Monoid for u64 {
    fn id() -> u64 {
        0
    }

    fn op(a: u64, b: u64) -> u64 {
        a.saturating_add(b)
    }
}

pub fn mean(v: &[u64]) -> u64 {
    let (left, right) = v.split_at(v.len() / 2);
    let (a, b) = rayon::join(|| par_sum(left), || par_sum(right));
    (a + b) / v.len() as u64
}
```

- **信用する部分**（本体は検証しない）
  - `par_sum<T: Monoid>(v)`: rayon の `reduce(T::id, T::op)` を包む。事前条件は「`T` の `op` が結合的で、`id` が左右の単位元である」。rayon の `reduce` のドキュメントが、`op` が結合的であること、`identity()` が真の単位元であることを求めているので、それをそのまま事前条件にした。事後条件は「結果は順の畳み込み `fold_spec(v)`」。
  - `rayon::join`: 「2 つのクロージャを実行し、それぞれの結果を返す」。
- **`sum()` ではなく `reduce` を使う理由:** rayon の `sum()` は、標準の `Sum` トレイトの実装で足し合わせるので、`Monoid` の `op` とは結び付かない。`reduce` は、単位元と演算を直接受け取る。
- **使う側のモノイド:** u64 の飽和加算（`saturating_add`、単位元 0）。飽和加算は結合的で（どちらの順でも `min(a + b + c, u64::MAX)` になる）、0 は左右の単位元である。
- **検証する自分の関数:** `mean(v: &[u64]) -> u64`（平均。小数点以下切り捨て）
  - 実装: `split_at` で半分に分け、`join` で両半分の `par_sum` を並列に求め、足して要素数で割る。
  - 事前条件: 「空でない」かつ「和 `sum(v)` が u64 に収まる」。前者がなければゼロ除算になる。後者がなければ、飽和して結果が平均と異なるか、`a + b` がオーバーフローする。
  - 事後条件: 「結果は `sum(v) / len`」。
- **事前条件を満たさない呼び出し:** 4.12 節の `Diff`（差の絶対値。結合的でない）で `par_sum` を呼ぶ `diff_sum`。検証で弾かれなければならない。

```rust
pub fn diff_sum(v: &[Diff]) -> Diff {
    par_sum(v)
}
```

#### Kani

**書けない。** 外部の関数の仕様を宣言して信用する仕組みがなく、スタブで代わりの実装に差し替えることしかできない。`par_sum` の事前条件も書けず、`diff_sum` は拒否されない。さらに、調べられるのは長さを限ったスライスだけである。

```rust
// rayon はスレッドを使うので検証できない。par_sum と rayon::join を逐次版に差し替え、その振る舞いを信用する
#[cfg(kani)]
fn seq_sum<T: Monoid>(v: &[T]) -> T {
    let mut acc = T::id();
    for &x in v {
        acc = T::op(acc, x);
    }
    acc
}

#[cfg(kani)]
#[kani::proof]
#[kani::stub(par_sum, seq_sum)]
#[kani::stub(rayon::join, seq_join)]
#[kani::unwind(5)]
fn check_mean() {
    let arr: [u64; 4] = kani::any();
    let v = kani::slice::any_slice_of_array(&arr);
    kani::assume(!v.is_empty());
    let total = v.iter().try_fold(0u64, |s, &x| s.checked_add(x));
    kani::assume(total.is_some());
    assert_eq!(mean(v), total.unwrap() / v.len() as u64);
}
```

- Kani で外部ライブラリを信用する仕組みは、関数スタブ（`#[kani::stub(元の関数, 差し替え先)]`、`Cargo.toml` の `[package.metadata.kani] unstable = { stubbing = true }`）だけ。`par_sum` を順に畳み込む関数に、`rayon::join` を 2 つのクロージャを順に呼ぶ関数に差し替えた。「rayon は順の畳み込みと同じ結果を返す」という信用は、宣言した仕様ではなく、差し替えた実装として表れる。
- 調べたのは長さ 1〜4 のスライスだけ。
- スタブなしのハーネス（コメントアウト済み）は、4.10 節と同じく Kani の内部エラー（`Kani unexpectedly panicked during compilation`）で止まる。
- 結果: `Complete - 1 successfully verified harnesses, 0 failures, 1 total.`

#### Creusot

```rust
// 本体は検証しない。T がモノイドなら、rayon の並列の畳み込みが順の畳み込みと等しいことを信用する
#[trusted]
#[ensures(result == fold_spec(v@))]
pub fn par_sum<T: Monoid>(v: &[T]) -> T {
    v.par_iter().copied().reduce(T::id, T::op)
}

// 本体は検証しない。rayon::join が両クロージャを実行して結果を返すことを信用する
#[trusted]
#[requires(a.precondition(()) && b.precondition(()))]
#[ensures(a.postcondition_once((), result.0) && b.postcondition_once((), result.1))]
pub fn join<A, B, RA, RB>(a: A, b: B) -> (RA, RB)
where
    A: FnOnce() -> RA + Send,
    B: FnOnce() -> RB + Send,
    RA: Send,
    RB: Send,
{
    rayon::join(a, b)
}

impl Monoid for u64 {
    #[logic(open)]
    fn op_spec(a: u64, b: u64) -> u64 {
        pearlite! { if a@ + b@ > u64::MAX@ { u64::MAX } else { a + b } }
    }
    // id_spec、法則、id、op は 4.12 節の Max と同じ形
}

#[requires(0 < v@.len() && sum(v@) <= u64::MAX@)]
#[ensures(result@ == sum(v@) / v@.len())]
pub fn mean(v: &[u64]) -> u64 {
    let (left, right) = v.split_at(v.len() / 2);
    proof_assert!(v@.ext_eq(left@.concat(right@)));
    snapshot!(lemma_sum_concat(left@, right@));
    snapshot!(lemma_fold_sum(left@));
    snapshot!(lemma_fold_sum(right@));
    let (a, b) = join(move || par_sum(left), move || par_sum(right));
    (a + b) / v.len() as u64
}
```

- **信用する仕様の宣言:** `#[trusted]` を付けた関数は本体を検証せず、宣言した `requires` / `ensures` が信用される。
- **事前条件:** `par_sum` の事前条件（法則）は、4.12 節と同じくトレイト `Monoid` に置いた法則で書いた（`fold_spec` も 4.12 節と同じ。トレイトには `Send + Sync` を足した）。
- **事前条件を満たさない呼び出し:** `Diff` の `Monoid` の実装が `Goal Coma.vc_assoc_Diff: ✘` で拒否されるので、`diff_sum` は書けない。理由とともにコメントアウトした。
- クロージャには事前条件・事後条件を書いていないが、Creusot は本体から導いた。
- u64 の法則は、実装の側に本体が空の論理関数として書き、ソルバーが示した。`op` の `saturating_add` には、creusot-std が仕様を与えている。
- **補助:** `lemma_sum_concat`（連結の和は和の和）と `lemma_fold_sum`（飽和加算の畳み込みは、和が u64 に収まれば和に等しい）を、どちらも帰納法で示し、`join` の前に適用する。
- 実行すると、`saturating_add` の仕様の位置（標準ライブラリのソース）が見つからないという警告（`Warning: inexistent file in source location`）が出るが、証明は通る。
- 結果: `Proved (13 files) ✔`

#### Verus

```rust
// 本体は検証しない。T がモノイドなら、rayon の並列の畳み込みが順の畳み込みと等しいことを信用する
#[verifier::external_body]
pub fn par_sum<T: Monoid>(v: &[T]) -> (r: T)
    ensures
        r == fold_spec(v@),
{
    v.par_iter().copied().reduce(T::id, T::op)
}

// 本体は検証しない。rayon::join が両クロージャを実行して結果を返すことを信用する
#[verifier::external_body]
pub fn join<A, B, RA, RB>(a: A, b: B) -> (r: (RA, RB))
    where
        A: FnOnce() -> RA + Send,
        B: FnOnce() -> RB + Send,
        RA: Send,
        RB: Send,
    requires
        a.requires(()),
        b.requires(()),
    ensures
        a.ensures((), r.0),
        b.ensures((), r.1),
{
    rayon::join(a, b)
}

impl Monoid for u64 {
    open spec fn op_spec(a: u64, b: u64) -> u64 {
        if a + b > u64::MAX { u64::MAX } else { (a + b) as u64 }
    }
    // id_spec、法則、id、op は 4.12 節の Max と同じ形
}

pub fn mean(v: &[u64]) -> (r: u64)
    requires
        0 < v.len(),
        sum(v@) <= u64::MAX,
    ensures
        r == sum(v@) / v.len() as int,
{
    let (left, right) = v.split_at(v.len() / 2);
    proof {
        assert(v@ =~= left@ + right@);
        lemma_sum_concat(left@, right@);
        lemma_fold_sum(left@);
        lemma_fold_sum(right@);
    }
    let (a, b) = join(
        move || -> (s: u64)
            ensures
                s == fold_spec(left@),
            { par_sum(left) },
        move || -> (s: u64)
            ensures
                s == fold_spec(right@),
            { par_sum(right) },
    );
    (a + b) / v.len() as u64
}
```

- **信用する仕様の宣言:** `#[verifier::external_body]` を付けた関数は本体を検証せず、宣言した `requires` / `ensures` が信用される。
- **事前条件:** Creusot と同じく、4.12 節のトレイトの法則で書いた（`proof fn lemma_assoc` / `lemma_id`）。
- **事前条件を満たさない呼び出し:** `Diff` の `Monoid` の実装が、`lemma_assoc` の `postcondition not satisfied` で拒否されるので、`diff_sum` は書けない。理由とともにコメントアウトした。
- vstd は `u64::saturating_add` に、`returns` で値を与えている（`vstd/std_specs/num.rs`）。u64 の法則は、`proof fn` の本体を空のままソルバーが示した。
- Verus ではクロージャに `ensures` を明示した。その性質が、`join` の事後条件 `a.ensures((), r.0)` を通して `join` の結果に伝わる。
- 補題は Creusot と同じ 2 つ。
- 結果: `verification results:: 9 verified, 0 errors`

#### Aeneas

信用する関数の本体を Charon の `--opaque` で外し、仕様を Lean の `axiom` で書いた。`par_sum` の事前条件（法則）は axiom の仮定にした。

```lean
-- 本体は検証しない。T がモノイドなら、rayon の並列の畳み込みが順の畳み込みと等しいことを信用する
axiom par_sum_spec {T : Type} (inst : ParSum.Monoid T) (f : T → T → T) (e : T)
    (hop : ∀ a b, inst.op a b ⦃ r => r = f a b ⦄) (hid : inst.id ⦃ r => r = e ⦄)
    (hassoc : ∀ a b c, f (f a b) c = f a (f b c))
    (hidl : ∀ a, f e a = a) (hidr : ∀ a, f a e = a) (v : Slice T) :
    par_sum inst v ⦃ r => r = List.foldl f e v.val ⦄

@[step]
theorem par_sum_u64_spec (v : Slice U64) :
    par_sum U64.Insts.Par_sumMonoid v ⦃ r => r.val = min U64.max (sum v.val) ⦄

theorem mean_spec (v : Slice U64) (h0 : 0 < v.length) (h1 : sum v.val ≤ U64.max) :
    mean v ⦃ r => r.val = sum v.val / v.length ⦄
```

（`join_spec`、`sum_fits_u64` のループの仕様、飽和加算の補題と証明の全体は `aeneas/13_par_sum/proofs/ParSum/Properties.lean`。）

- **信用する仕様の宣言:** `par_sum` は、Charon の公式オプション `--opaque=crate::par_sum` で本体を変換対象から外した。Aeneas は `axiom par_sum {T : Type _} (MonoidInst : Monoid T) : Slice T → Result T`（中身のない関数）と、`rayon_core.join.join` の axiom を `FunsExternal_Template.lean` に出力する。その性質を、axiom `par_sum_spec` と `join_spec` で信用する。
- **事前条件は呼び出し側に課される。** `par_sum` には定義がないので、呼び出し側が `par_sum` について使える事実は `par_sum_spec` だけで、その仮定（法則）を示さなければ何も証明できない。4.12 節の `fold_halves`（定義を展開すれば仮定を迂回できる）とは、ここが違う。
  - `diff_sum v ⦃ _ => True ⦄`（失敗しない）を証明しようとすると、`par_sum_spec` の仮定 `hassoc`（結合律）が `agrind failed` で示せなかった（コメントアウト済み）。単位元の仮定と `hop` は示せる。
  - `unfold par_sum` は `Tactic unfold failed to unfold par_sum` で失敗し、定義を展開して迂回することもできない。
- **生成されたテンプレートが、そのままではビルドできない。** テンプレートは名前空間の外で `open ParSum` するので、`Monoid` が Mathlib の `_root_.Monoid` と曖昧になり、`Ambiguous term Monoid` で失敗する。テンプレートをコピーした `FunsExternal.lean`（README の手順で、利用者が埋めるファイル）で `ParSum.Monoid` と書いた。
- u64 の飽和加算が `par_sum_spec` の仮定（法則）を満たすことを示して、`par_sum_u64_spec` を証明した。Aeneas の Lean ライブラリの `saturating_add` には値についての補題がないので、`saturating_add_val`（値は `min U64.max (a + b)`）を自分で示した。
- `mean` の事前条件は `debug_assert!(!v.is_empty() && sum_fits_u64(v))` で書いた（`sum_fits_u64` は `checked_add` で和を求める検査関数）。
- `join` の性質は、Lean の関数が決定的なので、「`a` を実行してから `b` を実行した結果に等しい」という等式の axiom で書いた。
- 結果: `Build completed successfully`

4 ツールとも、`par_sum` の本体は本物の rayon を呼んでいて、通常のビルド（`cargo build` / `cargo verus build`）が通る。lib クレートでテストを置かない方針なので、実行時の動作確認はしていない。

### 4.14 glTF の読み込み（`14_load_gltf`）

**題材:** 実際の glTF 2.0 ファイル（`.gltf` の JSON と `.glb` のバイナリ）をバイト列から読み込み、仕様で要求される規則を満たすことを確かめる、実用的な読み込み処理を検証する。外部のクレートは使わず、パースそのものも検証の対象にした。

```
parse_gltf(bytes) -> Result<Gltf, GltfError>      // GLB コンテナ → JSON → スキーマの読み取り
validate(&Gltf)   -> Result<(), GltfError>        // 仕様の MUST の規則
load_gltf(bytes)  -> Result<Gltf, GltfError>      // parse_gltf → validate
process(&Gltf)                                     // 規則を満たす glTF を前提にした処理（本体は想定）
render(bytes)     -> Result<(), GltfError>        // load_gltf → process
render_unvalidated(bytes)                          // parse_gltf → process（検査しない。検証で弾かれるべき）
```

**実装:** Rust で約 3,500 行、251 関数、18 ファイル。3 ツールで同じコード（Aeneas 版だけ `process` の先頭に `debug_assert!` がある）。

- **GLB コンテナ**（仕様 4.4 節）: マジックナンバー、バージョン、長さ、チャンクの長さが 4 の倍数、JSON チャンクが最初で 1 つだけ、BIN チャンクは 2 番目だけ、知らない種類のチャンクは無視。
- **JSON**（RFC 8259）: 空白、リテラル、数値の字句、文字列のエスケープ（`\uXXXX` とサロゲートペア。単独のサロゲートは拒否）、文字列中の UTF-8 の検証（Unicode の Table 3-7）、入れ子の深さの上限（128）、先頭の BOM（RFC 8259 8.1 節で無視してよい）。JSON の木は、ノードを 1 つの `Vec` に並べてインデックスで子を指す形（アリーナ）にした。
- **整数の値:** 整数のプロパティは `1.0` や `1e2` とも書ける（仕様 2.7 節「小数部が 0 の小数や指数表記で書いてよい」）ので、数値の字句から有理数としての値を求め、整数かつ u64 に収まる場合だけを受け付ける。浮動小数点数は使わない。
- **スキーマの読み取り:** すべての種類のオブジェクトについて、公式の JSON スキーマの型・必須・既定値・`minItems` を確かめてモデルに読み込む。同じキーが重複したら後の値を使う（仕様 2.7 節）。使われている拡張の名前も集める。
- **妥当性の規則:** 仕様の原稿（`Specification.adoc`）から MUST・MUST NOT・REQUIRED を含む文 162 個を取り出し、文書の構造と整数だけで判定できる 107 個をすべて入れた（一覧と、検査しない 55 個の理由は付録 A）。
  - インデックスの範囲
  - ノードの階層が木になっていること（親は 1 つ以下、循環なし）と、シーンの根
  - メッシュ: 属性名の規則と型の表、属性の要素数の一致、モーフターゲット、モードごとの頂点数、インデックスのアクセサーの型、テクスチャ座標の存在
  - スキン: 関節の共通の祖先、骨格の根、逆バインド行列
  - アニメーション: 入力と出力のアクセサーの型、出力の要素数、ターゲットの重複
  - bufferView: 範囲、1 種類のデータだけを持つこと、ストライドと `target` の規則
  - アクセサー: bufferView に収まること、境界合わせ、行列の列のパディング、疎アクセサー
  - バッファー: GLB の BIN チャンクの長さ、data URL（RFC 2397、base64）の構文とメディアタイプとデコード後の長さ
  - 画像: `uri` と `bufferView` のどちらか一方、`mimeType`
  - URI の構文、カメラ、拡張の宣言（`extensionsUsed` と `extensionsRequired`）
  - このローダーが対応する範囲（メジャーバージョン 2、`minVersion`、要求される拡張なし、既知の成分型とモード）。範囲外は `Unsupported` を返す。
- **検査しないもの**（理由つき）:
  - 浮動小数点の値の範囲（`rotation` の範囲、カメラの `zfar > znear`、行列が TRS に分解できるか）。値は「数であること」と配列の長さだけを確かめる。
  - バッファーと画像の中身（`min`/`max` と実データの一致、インデックスの値、疎アクセサーのインデックスの昇順、ジョイントとウェイトの値、時刻の昇順、PNG/JPEG の形式）。バイナリのデータを読む必要があり、外部ファイルの読み込み（I/O）もしないため。
  - 仕様が SHOULD にとどまる規則（仕様にない属性名、32 ビット整数の属性、カメラの型と合わないプロパティ）。

**モジュールの構成:** 3 ツールで同じ分け方にした。どのツールにも、1 ファイルにまとめる必要はない（Creusot と Verus は普通の Rust の `mod` をそのまま扱い、Aeneas は Charon がクレート全体を 1 つの Lean のモジュールに翻訳する）。ファイルは、読む人が別々に探す単位（仕様の出典や、規則の分野）でだけ分けた。

| ファイル | 内容 |
|---|---|
| `lib.rs` | 公開する関数（`parse_gltf`、`load_gltf`、`process`、`render`、`render_unvalidated`） |
| `glb.rs` | GLB コンテナ（仕様 4.4 節） |
| `model.rs` | glTF のモデルの型と定数 |
| `json/mod.rs` | JSON のノード、空白、値のパーサー（RFC 8259） |
| `json/number.rs` | 数値の字句（RFC 8259 6 節）と整数の値（仕様 2.7 節） |
| `json/string.rs` | 文字列、エスケープ、UTF-8（RFC 8259 7 節、Unicode の Table 3-7） |
| `read/mod.rs`、`read/access.rs`、`read/objects.rs` | スキーマの読み取りの根と配列、プロパティの取り出し、オブジェクトごとの読み取り |
| `validate/mod.rs` | `validate`、規則の連言、asset・拡張・カメラの規則 |
| `validate/refs.rs`、`validate/support.rs` | 参照の範囲、対応範囲（`Unsupported`） |
| `validate/hierarchy.rs`、`mesh.rs`、`animation.rs`、`data.rs`、`resource.rs` | 規則（ノードの木・シーン・スキン、メッシュ、アニメーション、bufferView・アクセサー、URI・バッファー・画像） |
| `validate/util.rs` | 規則の検査で共通に使う補助 |

- 仕様と証明は、対象のコードと同じファイルに置いた。規則の定義は、それを検査する関数のすぐ近くにある。公開する関数の性質は `lib.rs` の契約に書き、そこで使う名前をたどれば定義に行き着く。Aeneas は、Rust のファイルごとに Lean のファイルを 1 つ置き、定義と定理を一緒に書いた（`Json/String.lean` など）。複数のファイルで使うタクティクと補題だけを `Common.lean` に置いた。
- 付録 A の MUST の番号を、規則を述べる仕様の定義と、それを証明する関数（Aeneas は定理）に `// MUST-016, MUST-017: …` の形のコメントで付けた。RFC 8259、RFC 2397、Unicode の Table 3-7、GLB の節も、同じ形で付けた。

**実装の確かめ方:** Khronos のサンプルモデル 7 個（`.gltf` と `.glb` の 13 ファイル）をすべて受け付けた。glTF-Validator のテスト集 263 ファイルと結果を比べ、一致しなかったものは、上の「検査しないもの」に当たるか、仕様の原稿の文が glTF-Validator より厳しいものだけだった。後者は次の 3 つ。

- 行列のアクセサーの最後の要素のパディングを省いたもの。仕様の式はパディングを含む要素の大きさを使う。
- 三角形の頂点数が 3 の倍数でないもの。仕様は MUST で、glTF-Validator は警告にとどめる。
- どこからも使われないアクセサーが、ストライド付きの bufferView を指すもの（`get_elements.gltf`）。MUST-038 は「頂点属性に使われないアクセサー」と書くので、使われないアクセサーも含めた。glTF-Validator は、このファイルをエラーにしない。画像の bufferView をアクセサーが使わないこと（MUST-027）も、同じように使われないアクセサーを含めた。

文の読み方を決めたものは、ほかに次の 2 つ。

- MUST-028（他の種類のデータに使う bufferView は `target` を持たない）は、使われないアクセサーだけが指す bufferView には当てはめない。そのデータは何にも使われないので、「他の種類のデータに使う」に当たらない。
- MUST-029 と MUST-039（2 つ以上の頂点属性が使う bufferView はストライドが必要）は、異なるアクセサーの数で数える。同じアクセサーを 2 つの属性が使っても、データは 1 つなので 1 と数える。

これらのファイルとテスト用のプログラムは、確かめたあと削除した。

**検証する性質**（3 ツールで共通。どれも前提なし）:

- `parse_gltf`: GLB なら、コンテナの仕様を満たさないとき、かつそのときに限り `Err(Glb)`。JSON の文法を満たさないとき、かつそのときに限り `Err(Json)`。それ以外は、スキーマの仕様と一致するモデルを返すか、スキーマの仕様に違反するときに限りエラー（対応しない書き方なら `Unsupported`、規則違反なら `Invalid`）。
- `validate`: `Ok(())` になるのは、参照・対応範囲・規則をすべて満たすとき、かつそのときに限る。
- `load_gltf`、`render`: 上の 2 つの組み合わせ。`process` の事前条件「規則を満たす」は `load_gltf` の結果から示せる。
- `render_unvalidated`: `parse_gltf` の結果は規則を満たすとは限らないので、`process` の事前条件を示せず、検証が失敗する。失敗を確かめたあとコメントアウトした。
- パニックしない（添字の範囲、算術のオーバーフロー、ゼロ除算）ことと、停止すること。

仕様は、作業中は 3 ツールで共通の文書にまとめ、各ツールの仕様はそれを書き写した（文書は作業後に削除した）。JSON の文法は RFC 8259 の規則の書き写し、妥当性の規則は ∀ と ∃ を使った宣言的な述語で、どちらもコードのループとは独立に書いた。

**内部の関数に置いた前提:** 公開する関数には前提がない。内部の関数には、それを呼ぶ関数が必ず満たす前提だけを置き、呼び出し側で示した。

- `number_to_u64`: 数値の各桁が 9 以下で、整数部・小数部・指数部の桁の列の長さの合計が usize の最大値以下（`parse_number` が満たす）。指数部の条件がないと、指数が u64 の最大値を超えて打ち切られる場合に結果が誤る（反例: 小数部が 2⁶⁴−1 桁で、指数が u64 の最大値 + 5）。
- スキーマの読み取りの関数: JSON の文書の整形性（子のインデックスが親より小さいこと。`parse_json` が満たす）。

#### 共通のコードを各ツールに合わせて変えた点

- **Creusot:** `Vec` を介した再帰型（`Json::Array(Vec<Json>)`）と、関数の相互再帰（値・配列・オブジェクトのパーサー）を受け付けない。ガイドの `termination.md` は、再帰型の中で自分自身を置けるのは `Box`・`&`・`&mut` の下だけとし、「相互再帰する関数は現在サポートしていない」としている。CHANGELOG の 0.12.0 には「相互再帰するプログラム関数に対応」とあるが、最小の `even`/`odd` でも `Mutually recursive functions` で弾かれた。そのため、JSON の木をアリーナにし、パーサーを自分自身だけを呼ぶ 1 つの再帰関数にした。
- **Aeneas:** 次の書き方は、関数の本体が翻訳されないか、中身のない axiom になる。そのため、ループを小さな関数に切り出す形に書き直した。
  - return を含むループのあとに、関数の結果になる式以外の処理が続く書き方（「Early returns inside of loops are not supported yet」「Breaks to outer loops are not supported yet」）
  - `Option` どうしの `==`（Lean のモデルがない）
  - 1 つの関数で 15 個の配列を読む部分は、Charon が約 38GB のメモリを使って止まったので、配列ごとの関数に分けた。
  - `match` の腕に比較だけを書いた `let`（`None => u.attribute_count[b] < 2`）は、型の注釈なしの `ok (… < …)` に翻訳され、Lean が `Prop` と推論してビルドできなかった。`bool` を返す関数に分けた。
- **Verus:** 次の 2 つは Verus の検証で見つかり、共通のコードで直した。
  - GLB のチャンクの番号 `let mut index = 0;` は、型の注釈がなく 0 と 1 との比較にしか使われないので i32 になっていた。チャンクが 2³¹ 個を超える入力（約 16 GiB）で `index += 1` がオーバーフローしてパニックする、実際のバグだった。`usize` にした。
  - `parse_string` の `j + 7 < s.len()` は、入力の長さが usize の最大値のときにオーバーフローする。同じ意味の `s.len() - j > 7` にした。直さないと、公開する関数に「入力の長さが isize の最大値以下」という前提が要る（Rust は保証するが、Verus は知らない）。

- **3 ツール共通:** 検証の途中で、次の 2 つも共通のコードで直した。
  - `validate` は任意のモデルを受け取るので、アクセサーの成分数が大きいと要素の大きさの計算がオーバーフローしうる。前提を足す代わりに、成分数と行列かどうかの整合を参照の検査に加えた（`read_gltf` が作るモデルは必ず満たす）。
  - 重複したキーのうち上書きされたものは、`extensions` でも値を検査しないようにそろえた。

#### Kani

作っていない（1.4 節）。

#### Creusot

```rust
#[ensures(match result {
    None => json_text_spec(s@) == None,
    Some(d) => doc_wf(d) && json_text_spec(s@) == Some(tree(d.nodes@, d.root@)),
})]
#[check(terminates)]
pub fn parse_json(s: &[u8]) -> Option<JsonDoc>

#[ensures(validate_res(*g, result))]
#[check(terminates)]
pub fn validate(g: &Gltf) -> Result<(), GltfError>

#[requires(valid(*_gltf))]
#[check(terminates)]
pub fn process(_gltf: &Gltf)
```

- 共通の性質をすべて証明した。250 関数すべてに `#[check(terminates)]` を付け、ループと再帰に減少量（`#[variant]`）を与えて、停止性まで証明した（`#[check(terminates)]` がないと、既定は「停止すれば正しい」という部分正当性）。
- **仕様の書き方:** 論理の側でも `Seq` を介した再帰型と相互再帰は使えない（`Recursive occurrence … under opaque type Seq`）。そのため、JSON の抽象的な値は `Box` でつないだリストで表した。値・配列・オブジェクトの文法は、モードを引数にとる 1 つの論理関数 `gram(mode, kind, s, i, d)` にまとめた。スキーマの読み取りは「j を X として読むと x になる」という関係で書いた。
- **手間:** 実行コードのキーの配列と仕様の `seq![..]` が別の項になるので、キーごとの補題を約 70 個用意した。大きな検証条件は、中間の `proof_assert!` で分割した。
- **定義の見え方:** 論理関数の本体は、`open` でなければ定義したモジュールの中だけで見える。数値の値（`dval`）と JSON の文法（`gram` など）は、本体が見えると再帰の定義の公理が証明の文脈に入り、`number_to_u64` と `parse_value` の証明が通らなくなった（`open` にすると、`parse_gltf` も通らなくなった）。そのため、この 2 つは、本体を使う補題と一緒に、同じファイルの中の `mod opaque` に入れて隠した。
- `render_unvalidated`: `Goal Coma.vc_render_unvalidated: ✘` の `[process requires] goal: valid …` で失敗する。
- 規模: コード・仕様・証明を合わせて約 10,800 行。
- 結果: `Proved (450 files) ✔`（キャッシュなしで約 2 分 30 秒）
- 負荷への弱さ: why3find はプルーバーに時間制限をかける（このプロジェクトの `why3find.json` は既定のままで `"time": 1.0`）。ほかの処理でマシンの負荷が高い（load average 15〜34）と、時間のかかるゴールが制限を超え、実行ごとに違うゴールが 1 つ失敗した。失敗はキャッシュに残り、`--no-cache` で再実行するまで続く。並列数を下げる（`--why3find-arg=-j --why3find-arg=6`）と通った。

#### Verus

```rust
pub fn parse_json(s: &[u8]) -> (r: Option<JsonDoc>)
    ensures
        match r {
            Some(doc) => json_text(s@) == Some(tree(doc.nodes@, doc.root as int)) && doc_wf(doc),
            None => json_text(s@) is None,
        },

pub fn validate(g: &Gltf) -> (r: Result<(), GltfError>)
    ensures
        r is Ok == valid(g@),
        r matches Err(GltfError::Unsupported) ==> refs_ok(g@) && !supported_s(g@),
        r matches Err(GltfError::Invalid) ==> !refs_ok(g@) || (supported_s(g@) && !rules_ok_s(g@)),

pub fn process(_gltf: &Gltf)
    requires
        valid(_gltf@),
```

ノードの階層の規則は、次のように宣言的に書いた。

```rust
pub open spec fn h1(g: GltfS) -> bool {
    forall|p1: int, k1: int, p2: int, k2: int|
        0 <= p1 < g.nodes.len() && 0 <= k1 < g.nodes[p1].children.len() && 0 <= p2 < g.nodes.len() && 0 <= k2
            < g.nodes[p2].children.len() && #[trigger] g.nodes[p1].children[k1] == #[trigger] g.nodes[p2].children[k2]
            ==> p1 == p2 && k1 == k2
}

pub open spec fn h2(g: GltfS) -> bool {
    forall|n: int| 0 <= n < g.nodes.len() ==> #[trigger] reaches_root(g, n)
}
```

- 共通の性質をすべて証明した。すべてのループと再帰に `decreases` を付けたので、停止性も証明される。
- **仕様の書き方:** JSON の抽象的な値は `Seq` を介して再帰する型。文法は「位置 i から値 v が書かれていれば、その終わりの位置を返す」という関係（値の構造についての再帰）で書き、読める値が 1 つに決まることを補題で示した。
- **手間:** 同じ形のラムダ式を 2 か所に書くと等しいと示せないので、名前付きの spec 関数にした。ループごとに前の事実を引き継がないので、補題の呼び出しをループの中で繰り返した。ビット演算には `bit_vector`、数値の証明には `nonlinear_arith` を使った。`read_gltf` は SMT の資源の上限（`rlimit`）を上げた。
- `render_unvalidated`: 既定の資源の上限では `rlimit exceeded` で止まり、一時的に上限を上げると `error: precondition not satisfied`（`valid(_gltf@)`）で失敗する。
- 規模: コード・仕様・証明を合わせて約 13,900 行。
- 結果: `verification results:: 528 verified, 0 errors`（約 20 秒）

#### Aeneas

```rust
pub fn process(gltf: &Gltf) {
    debug_assert!(matches!(validate(gltf), Ok(())));
    // ジオメトリ処理を行う想定。参照がすべて範囲内で、仕様の規則を満たすことを前提にする
}
```

```lean
theorem parse_json_spec (s : Slice U8) :
    json.parse_json s ⦃ r => match r with
      | none => jsonText s.val = none
      | some doc => jsonText s.val = some (tree doc doc.root.val) ∧ docWf doc ⦄

theorem validate_spec (g : model.Gltf) :
    validate.validate g ⦃ r => (r = .Ok () ↔ valid g) ∧
      (r = .Err .Unsupported → refsOk g ∧ ¬ supportedSpec g) ∧
      (r = .Err .Invalid → ¬ refsOk g ∨ (supportedSpec g ∧ ¬ rulesSpec g)) ∧
      r ≠ .Err .Glb ∧ r ≠ .Err .Json ⦄

theorem parse_gltf_spec (bytes : Slice U8) : parse_gltf bytes ⦃ r => ParseGltfSpec bytes.val r ⦄

theorem load_gltf_spec (bytes : Slice U8) : load_gltf bytes ⦃ r => LoadGltfSpec bytes.val r ⦄
```

- 共通の性質をすべて証明した。翻訳された関数は `partial_fixpoint` で定義され、`⦃ ⦄` の仕様は「失敗も発散もせずに結果を返す」ことを含むので、停止性も証明される。生成された Lean（約 11,900 行）には axiom がなく、手を加えていない。
- **事前条件の課し方:** 5.2.2 節のとおり、`process` の事前条件は `debug_assert!` で書いた。`render_unvalidated` の定理を証明しようとすると、`process` の `massert` の所で、`parse_gltf` の事後条件から `valid g` を示すゴールが残る。証明できないことを確かめたあと、コメントアウトした。
- **仕様の書き方:** JSON の抽象的な値は `List` を介して入れ子になる帰納型。文法は Verus と同じく関係で書いた。
- **Verus・Creusot より厳密な点:** Aeneas の `Vec::push` は、長さが上限を超えると失敗する。JSON の文書の整形性はノードの共有を禁じていないので、同じノードを何度も指す文書では、拡張の名前を集める処理の `push` が上限を超えうる。そこで `read_gltf` には「値の木のノード数が usize の最大値以下」という前提を置き、`parse_gltf` の中で「値の木のノード数は入力の長さ以下」を示して解消した。Verus と Creusot の `Vec::push` は、容量の上限をモデルに含めない。
- **手間:** `step*` は、束縛の中の `match`/`if` や、`index_mut` が返す組で止まる。これを越えるための補助マクロや補題を、層ごとに書いた。`simp_all` が再帰の上限に達したり、Mathlib の合同規則のせいで深い bind の列で止まったりする場面もあった。`utf8_len` は翻訳後に約 760 行・173 通りの場合分けになり、Table 3-7 を直接当てはめると時間切れになるので、コードの形に合わせた中間の定義を挟んだ。数値のパーサーの定理 1 つに、`maxHeartbeats` の上限を大きく上げる必要があった。
- 規模: 手で書いた仕様と証明が約 11,900 行。
- 結果: `Build completed successfully`（証明のビルドに約 10 分）

#### 3 ツールの比較

| | Creusot | Verus | Aeneas |
|---|---|---|---|
| 共通の性質 | すべて証明 | すべて証明 | すべて証明 |
| コードの調整 | アリーナ、再帰の 1 本化（再帰型と相互再帰が使えないため） | なし（バグ 2 件を検出） | ループの切り出し、関数の分割、`Option` の比較（翻訳の制限） |
| 事前条件の課し方 | `#[requires]` | `requires` | `debug_assert!`（`massert`） |
| 行数（仕様・証明を含む） | 約 10,800 | 約 13,900 | 約 11,900（仕様と証明）＋ 生成コード約 11,900 |
| 検証の時間 | 約 2 分 30 秒 | 約 20 秒 | 約 10 分 |

検証の時間は、3 つを順に 1 つずつ実行して測った（Creusot はキャッシュなし、Aeneas は証明のファイルをすべてビルドし直した時間）。ほかの処理でマシンの負荷が高い状態（load average 約 10〜13）での値。

### 4.15 PCG64 と [0, 1) の f32 の一様乱数（`15_pcg_float`）

**題材:** 乱数生成器 PCG64 の `next_u64` と、その u64 を `[0, 1)` の f32 に変換する方法を検証する。

**使う側から見たインタフェース:** 4 ツールで同じ、外部のクレートを使わない 1 ファイル（約 55 行）。

| 関数 | 入力 | 出力 |
|---|---|---|
| `Pcg64::new(state: u128, stream: u128) -> Pcg64` | 初期状態とストリーム番号 | 乱数生成器 |
| `Pcg64::next_u64(&mut self) -> u64` | 生成器 | 一様な u64 を 1 つ（生成器を 1 歩進める） |
| `Pcg64::next_f32_mul(&mut self) -> f32` | 生成器 | `next_u64` を 1 回呼び、乗算法で `[0, 1)` の f32 にしたもの |
| `Pcg64::next_f32_dense(&mut self) -> f32` | 生成器 | `next_u64` を 1 回呼び、Reynolds の方法で `[0, 1)` の f32 にしたもの |
| `u64_to_f32_mul(x: u64) -> f32` | u64 を 1 つ | 乗算法の変換 |
| `u64_to_f32_dense(x: u64) -> f32` | u64 を 1 つ | Reynolds の方法の変換 |

**PCG64:** rand_pcg 0.9 の `Lcg128Xsl64`（PCG XSL RR 128/64 (LCG)）と同じ。

- 状態は 128 ビット、増分は `(stream << 1) | 1`（奇数）、遷移は `s ← A·s + c (mod 2^128)`、出力は `rotr64((s >> 64) ^ s, s >> 122)`。
- 回転は、Verus と Creusot に `u64::rotate_right` の仕様がないので、PCG の参照実装（C）と同じくシフトで書いた。
- 4 つの初期値で 10 万個ずつ、rand_pcg 0.9.0 の `Pcg64` と出力が一致することを確かめた。

```rust
pub fn next_u64(&mut self) -> u64 {
    self.step();
    output_xsl_rr(self.state)
}

fn output_xsl_rr(state: u128) -> u64 {
    let rot = (state >> 122) as u32;
    let xsl = ((state >> 64) as u64) ^ (state as u64);
    (xsl >> rot) | (xsl << ((64 - rot) & 63))
}
```

**u64 を f32 にする 2 つの方法:**

- **乗算法:** 上位 24 ビットを整数として f32 にし、2^-24 を掛ける。結果は 2^-24 の倍数（2^24 通り）だけで、1/2 未満の f32 の多くは出ない。
  - rand 0.9 の標準（`rng.random::<f32>()`、`StandardUniform`）も乗算法。ソースのコメントは「Multiply-based method; 24/53 random bits」。
  - ただし rand は u32 を 1 つ引いて上位 24 ビットを使う。PCG64 の `next_u32` は `next_u64() as u32`（下位 32 ビット）なので、使うビットは今回のコードと違う。

  ```rust
  const SCALE: f32 = 1.0 / 16777216.0;

  pub fn u64_to_f32_mul(x: u64) -> f32 {
      ((x >> 40) as f32) * SCALE
  }
  ```

- **Reynolds の方法**（Reynolds 2017、"Dense uniform floats" の `rng_pdense_f32`）: 浮動小数点数の間隔の違いを考慮する Walker の方法（Walker 1974、Downey 2007）を、u64 1 つで済むようにしたもの。
  - **Walker の方法:** 乱数ビットの先頭に 0 が z 個続く確率 2^-(z+1) が、区間 `[2^-(z+1), 2^-z)` の幅と同じであることを使う。z で指数を、続く 23 ビットで仮数を選ぶと、各 f32 がその幅（次の f32 までの距離）に比例した確率で出る。必要なビット数は入力によって変わり、f32 では最悪 149 ビット要る。
  - **Reynolds の方法:** u64 1 つで、先頭の 0 が 40 個以下（確率 1 − 2^-40）なら Walker の方法と同じく指数と仮数（下位 23 ビット）を決める。それ以外は、下位 32 ビットに 2^-64 を掛ける。結果として、[2^-41, 1) の f32 はすべて、幅に比例した確率で出る。[0, 2^-41) では 2^-64 の倍数だけが出る。元のコードのコメントは「[2^-40, 1) は密」だが、z = 40 の区間 [2^-41, 2^-40) も密になる。
  - **u64 1 つでは原理的にここまで:** 入力は 2^64 通りなので、どの出力の確率も 2^-64 の倍数になる。間隔が 2^-64 より細かい 2^-41 未満の f32 には、幅のとおりの確率を与えられない。

  ```rust
  const SCALE_TINY: f32 = 1.0 / 18446744073709551616.0;

  pub fn u64_to_f32_dense(x: u64) -> f32 {
      let z = x.leading_zeros();
      if z <= 40 {
          f32::from_bits(((126 - z) << 23) | ((x as u32) & 0x7F_FFFF))
      } else {
          ((x as u32) as f32) * SCALE_TINY
      }
  }
  ```

**検証する性質:**

| | 性質 |
|---|---|
| P1 | `next_u64`（と `new`）がパニックせずに値を返す |
| P2 | 状態の周期がちょうど 2^128。増分 c が奇数のとき、すべての状態 s で `f^[2^128](s) = s`、`0 < n < 2^128` なら `f^[n](s) ≠ s`（Hull–Dobell の定理の m = 2^128 の場合） |
| P3 | 出力（u64 の列 `o_k`）の周期がちょうど 2^128。`o_{k+2^128} = o_k`、`0 < n < 2^128` なら `o_{k+n} ≠ o_k` となる k がある |
| P4 | 1 周期の中で、各 u64 の値がちょうど 2^64 回出る（PCG の論文 2.1.1 節の「uniformity」） |
| P5 | 返す f32 が NaN・±∞ でない |
| P6 | 返す f32 が厳密に `0 ≤ r < 1` |
| P7 | `[0, 1)` の一様乱数である（入力の u64 が一様のとき） |

P7 は次のように定めた。

- **確率の意味:** 変換は u64 x の決定的な関数 r(x)。「x が一様」は、2^64 通りの x がどれも同じ確率で出ること。したがって、f32 の値 v が出る確率は `#{x | r(x) = v} / 2^64`。
- **P7（本来の性質）:** 浮動小数点数の間隔の違いを考慮し、各 f32 の値 v に、その幅（次の f32 までの距離 `succ(v) − v`）のとおりの確率を与えること。`#{x | r(x) = v} = (succ(v) − v)·2^64`。これが成り立てば、f32 の lo ≤ hi について `P(lo ≤ r < hi) = hi − lo`（区間ごとに正しい確率）になる。u64 1 つでは、上のとおり 2^-41 未満では成り立たせられないので、Reynolds の方法が満たすべきなのは次の性質。
  - v ≥ 2^-41 なら、`#{x | r(x) = v} = (succ(v) − v)·2^64`。
  - v < 2^-41 なら、v は 2^-64 の倍数のときだけ出て、そのとき `#{x | r(x) = v} = 1`。
- **乗算法は P7 を満たさない。** 結果は 2^-24 の倍数だけなので、たとえば 2^-25 を返す x は 0 個で、P7 が求める 2^40 個にならない。乗算法について成り立つのは、2^-24 の倍数 k·2^-24 がそれぞれ 2^40 個の x から出る、という格子上の一様性だけ。

**先行事例:**

- **LCG の周期:** Hull と Dobell（1962）の定理、Knuth の TAOCP 第 2 巻 3.2.1.2 節の定理 A。どちらも紙の上の証明で、Coq・Isabelle・Lean で形式化したものは見つからなかった。Mathlib にもないが、極小周期の補題（`Function.minimalPeriod_eq_prime_pow` など）はある。
- **PCG:** O'Neill（2014）が、XSL RR 128/64 の周期は 2^128 であること（表）と、周期全体で各出力が同じ回数ずつ出るという性質（2.1.1 節）を述べている。LCG の周期については Hull と Dobell の論文を引用していて、証明は書いていない。
- **浮動小数点の一様乱数:** Walker（1974）、Downey（2007）、Reynolds（2017）、Goualard（2020、2022）、Pharr（2022）。いずれも紙の上の議論。Saad と Lee（PLDI 2025）は、浮動小数点の分布から正確に標本をとる生成器を作るが、`[0, 1)` への変換を証明支援系で証明した例は見つからなかった。

**証明の筋道（P2〜P4）:**

- **P2:** `f^[n](s) − s ≡ S_n·((A−1)s + c) (mod 2^128)`（`S_n = 1 + A + … + A^(n−1)`）。`(A−1)s + c` は奇数なので、`f^[n](s) = s ⇔ 2^128 | S_n`。A ≡ 1 (mod 4) から `S_{2^j} = 2^j·(奇数)`（Verus と Creusot は、より一般の「`2^k | S_n ⇔ 2^k | n`」を示した）。
- **P3:** `f^[2^127](x) = x + 2^127` は状態の最上位ビットだけを反転し、そのとき出力は必ず変わる（回転量のビット 5 と xor の値のビット 63 が同時に変わるので、元の出力と一致しない）。2^128 未満の周期 n があれば、それと 2^128 の最大公約数（2^127 の約数）も周期になり、2^127 も周期になって矛盾する。
- **P4:** 上位 64 ビットを固定すると、出力は下位 64 ビットの全単射なので、各値の逆像は 2^64 個の状態。P2 より、1 周期の 2^128 個の状態は互いに異なり、すべての状態を 1 回ずつ通る。

**結果:**

| | Kani | Creusot | Verus | Aeneas |
|---|---|---|---|---|
| P1 パニックしない | ○ | ○ | ○ | ○ |
| P2 状態の周期 2^128 | × | ○ | ○ | ○ |
| P3 出力の周期 2^128 | × | ○ | ○ | ○ |
| P4 各値が 2^64 回 | × | ○ | ○ | ○ |
| P5・P6 乗算法 | ○ | × | × | × |
| P5・P6 Reynolds の方法 | ○ | × | × | × |
| P7 Reynolds の方法 | × | × | × | × |
| P7 乗算法 | 性質が成り立たない（方法の性質） | 同左 | 同左 | 同左 |

- **P7 はどのツールでもできない。** 個数（確率）を書く手段と、f32 の値を正確に扱う手段の両方が要る。
  - Kani は f32 の値を正確に扱えるが、個数も確率も書けない。
  - Creusot・Verus・Aeneas は個数を書けるが、f32 を扱えない。
- **違反の検出:** 次のようなコードの変更で、各ツールの検証が失敗することを確かめた（確かめたあとコードは元に戻した）。
  - `new` の `| 1` を外す
  - 乗数を ≡ 3 (mod 4) に変える
  - 回転・シフトの量を 1 ずらす
  - `SCALE` を 2^-23 にする（Kani）
  - Reynolds の方法の `126 - z` を `127 - z` にする（Kani）

#### Kani

ハーネスは `kani::any()` の状態・入力についての `assert!`（関数の契約は不安定機能なので使わない）。`Complete - 7 successfully verified harnesses, 0 failures, 7 total.`（約 5 秒）。

- **P1:** 任意の状態と増分で `next_u64` を呼び、パニック（オーバーフロー・シフト量）がないことを確かめた。出力が `rotate_right` で書いた XSL RR と一致することも確かめた。
  - 「新しい状態 = A·s + c」も確かめようとしたが、128 ビットの乗算回路 2 つが等しいことを SAT ソルバーで示すことになり、既定のソルバーで 58 分たっても終わらなかった（kissat・cadical でも 5 分で打ち切り）。
  - `--cbmc-args --z3`（不安定オプションと外部のソルバー）では 0.03 秒で終わるが、既定の機能だけを使う方針（1.2 節）なので使っていない。このハーネスは理由を添えてコメントアウトした。
  - これは P2 以降につなぐための性質で、P1（パニックしない）そのものではない。
- **P2〜P4: 書けない。** 状態を最大 2^128 回進めるループが要るが、Kani はループを決めた回数までしか展開できない（`#[kani::unwind]`）。
  - `while n < 1 << 127 { g.step() }` は `unwinding assertion loop 0` で失敗する。
  - ジャンプアヘッドの閉じた式で代わりに計算すると、本物の `step` を繰り返すことの検証にならない。両者が等しいことを示すには帰納法が要る。
- **P5・P6:** 任意の x で、`r.is_finite()` と `0.0 <= r && r < 1.0` を確かめた（2 つの方法とも）。`next_f32_mul` / `next_f32_dense` も、任意の状態で確かめた。

  ```rust
  fn check_dense_range() {
      let r = u64_to_f32_dense(kani::any());
      assert!(r.is_finite());
      assert!(0.0 <= r && r < 1.0);
  }
  ```

- **P7: 書けない。** P7 は x の個数（確率）についての性質で、Kani には個数も確率も書く手段がない。ハーネスで書けるのは、入力ごとに成り立つ性質だけ。乗算法については、任意の x で `r as f64 == (x >> 40) as f64 / 16777216.0`（f64 では正確）を確かめた。r が丸めなしの (x >> 40)·2^-24 で、2^-24 の倍数でない f32（2^-25 など）は返らないので、乗算法が P7 を満たさないことの根拠になる。

#### Creusot

`Proved (53 files) ✔`（キャッシュなしで約 7 秒）。すべての関数に `#[check(terminates)]`。

- **P1:** 増分が奇数であることを型の不変条件（`Invariant`）にした。`next_u64` の事後条件は「新しい状態 = `lcg(古い状態, 増分)`、出力 = `out(新しい状態)`」。
- **P2・P3:** `Int` の上の論理関数と補題で証明した。仕様の f^[n] と k 回目の出力は、`next_u64` の契約を通してコードにつながる。

  ```rust
  #[logic(opaque)]
  #[requires(c@ % 2 == 1)]
  #[ensures(lcg_n(m128(), s, c) == s)]
  #[ensures(0 < n && n < m128() ==> lcg_n(n, s, c) != s)]
  pub fn p2_state_period(s: u128, c: u128, n: Int)

  #[logic(opaque)]
  #[requires(c@ % 2 == 1)]
  #[ensures(k >= 0 ==> out_k(k + m128(), s, c) == out_k(k, s, c))]
  #[ensures(0 < n && n < m128() ==> exists<j> j >= 0 && out_k(j + n, s, c) != out_k(j, s, c))]
  pub fn p3_output_period(s: u128, c: u128, k: Int, n: Int)
  ```

- **P4:** 有限集合 `FSet<Int>` の要素数で書いた（`FSet::interval(0, m128()).filter(|k| out_k(k, s, c) == v).len() == pw(64)`）。
  - 単射な写像で要素数が変わらないことを、帰納法で示した。
  - P2 から 1 周期の状態がすべての状態になることを、Why3 の `subset_eq` で示した。
  - 「最上位ビットが異なる状態の出力は異なる」などのビット演算の事実は、`#[bitwise_proof]` で証明した。
- **P5〜P7: 書けない。** 2 つの理由がある。
  - 整数から f32 への変換を、コードでも仕様でも翻訳できない。コードでは `error: Unsupported pointer cast: move _4 as f32 (IntToFloat)`（`creusot/src/translation/function/statement.rs` 197〜210 行）。仕様では `error: unsupported cast from u64 to f32 (allowed: bool as integer, integer as integer, or pointer as pointer)`。
  - `f32::from_bits` に仕様がない。`#[check(terminates)]` の関数から呼ぶと `called program function core::f32::<impl f32>::from_bits in program (terminates) context` になる。外すと「impossible precondition」の警告が出て、検証が失敗する。
- **仕様で書ける f32 の操作が足りない。** 仕様で使えるのは f32 の比較だけ（4.3 節）。`is_nan` は `called program function … in logic context` になる。`result@` は `Cannot take the view of f32`、`*` は `Cannot multiply f32 by f32 in logic` になる。
- **f32 の関数は検証の対象から外した。** 翻訳できない関数が 1 つでもあるとクレート全体を検証できないので、f32 の関数に `#[cfg(not(creusot))]` を付けた（Aeneas の `--exclude` と同じ扱い）。
- 規模: 約 800 行（共通のコードは約 55 行）。

#### Verus

`verification results:: 76 verified, 0 errors`（約 5 秒）。

- **P1:** 増分が奇数であることを `#[verifier::type_invariant]` にした。`next_u64` の事後条件は、Creusot と同じ形。
- **P2〜P4:** spec 関数と proof 関数で証明した。
  - P4 は vstd の `Set` の要素数で書き、`lemma_map_size` などの集合の補題を使った。
  - ビット演算の事実は `by (bit_vector)` で証明した。

  ```rust
  pub proof fn lemma_state_period(s: int, c: int)
      requires 0 <= s < m128(), 0 <= c < m128(), c % 2 == 1,
      ensures iter(m128() as nat, s, c) == s,
              forall|n: nat| 0 < n < m128() ==> iter(n, s, c) != s,

  pub proof fn lemma_output_period(s: int, c: int)
      requires 0 <= s < m128(), 0 <= c < m128(), c % 2 == 1,
      ensures has_period(s, c, m128() as nat),
              forall|n: nat| 0 < n < m128() ==> !has_period(s, c, n),

  pub proof fn lemma_uniform(s: int, c: int)
      requires 0 <= s < m128(), 0 <= c < m128(), c % 2 == 1,
      ensures forall|v: u64| occ(s, c, v).len() == pow2(64),
  ```

- **P5〜P7: 乗算法は書けるが、証明できない。**
  - 乗算法の事後条件 `!r.is_nan_spec() && !r.is_infinite_spec()`、`r.ieee_ge(0.0f32) && r.ieee_lt(1.0f32)`、`r as real * 16777216real == (x >> 40) as real` は書けるが、どれも `postcondition not satisfied` で失敗する。
  - 実行コードの `as f32` と `*` の結果は未解釈関数（`float_cast_spec`、`mul_ensures`）で、仕様側の IEEE の演算と結びついていない（`vstd/float.rs` 117〜130 行、`vstd/std_specs/ops.rs` 737〜776 行）。`SCALE` を 2^-23 にしても検証は通る。
- **Reynolds の方法は書けもしない。** `f32::from_bits` は `is not supported (note: you may be able to add a Verus specification to this function with assume_specification)` になる。`assume_specification` は自分で公理を足すことなので使わない。そのため、`u64_to_f32_dense` と `next_f32_dense` は `verus!` の外に置いた。
- **コードの置き方の違い:** `SCALE` などの f32 の定数を普通の `const` にすると「expected pure mathematical expression」になる（f32 の除算を spec の式にしようとする）ので、`exec const` にした。
- 規模: 約 950 行。

#### Aeneas

`lake build` は `Build completed successfully`（証明のファイルのビルドに約 12 秒）。主な定理が依存する公理は `propext`、`Classical.choice`、`Quot.sound` だけ。

- **P1〜P4:** `new` で作り、`next_u64` を何回か呼んだ生成器 p について証明した。
  - `run n p` は `next_u64` を n 回呼んだ結果、`nthOut p k` は k 回目の出力。
  - P2 には Mathlib の `Function.minimalPeriod_eq_prime_pow` を使い、P4 は `Finset.card` で書いた。

  ```lean
  theorem state_period (st sm : U128) (m : ℕ) (p0 p : Pcg64)
      (h0 : Pcg64.new st sm = ok p0) (hm : run m p0 = ok p) :
      run (2 ^ 128) p = ok p ∧ ∀ n, 0 < n → n < 2 ^ 128 → run n p ≠ ok p

  theorem output_period … :
      (∀ k, nthOut p (k + 2 ^ 128) = nthOut p k) ∧
      ∀ n, 0 < n → n < 2 ^ 128 → ∃ k, nthOut p (k + n) ≠ nthOut p k

  theorem output_uniform … (v : U64) :
      ((Finset.range (2 ^ 128)).filter (fun k => nthOut p k = ok v)).card = 2 ^ 64
  ```

- **P5〜P7: 変換できない。**
  - f32 の関数をそのまま変換すると、`[Error] Improperly typed constant value`（f32 の定数）と `[Error] Invalid inputs for binop`（`*`）で終了する。
  - 出力された Lean の `F32` は Aeneas のライブラリにない型で、自動束縛された型変数になる。`f32::from_bits` は中身のない axiom になる。
  - そのため、Charon の `--exclude` で f32 の項目を変換から外した。メソッドは `--exclude=crate::Pcg64::next_f32_mul` では一致しなかった（Charon の名前の照合が固有の impl に未対応。`charon/src/name_matcher/mod.rs` 269 行付近の `// TODO`）。`crate::_::next_f32_mul` の形で外した。
- 規模: 手で書いた証明が約 570 行。

#### 4 ツールの比較

- **PCG の周期と一様性（P2〜P4）:** 「すべての状態について 2^128 回」という性質なので、帰納法と数論の補題が要る。Creusot・Verus・Aeneas はどれも証明できた。Kani はループの展開回数に限りがあるので書けない。
- **f32（P5・P6）:** 実行コードの f32 の演算を正確にたどれるのは Kani だけで、Kani だけが証明できた。
  - Creusot は、整数から f32 への変換と `from_bits` を翻訳できない。
  - Verus は、仕様側に IEEE の演算はあるが、実行コードの演算と結びついていない。
  - Aeneas は f32 を変換できない。
- **一様性（P7）:** 個数（確率）を書く手段と、f32 の値を正確に扱う手段の両方が要る。Kani には前者がなく、Creusot・Verus・Aeneas には後者がないので、どのツールでもできない。
- **前提の違い:** P7 は「入力の u64 が一様」を前提にした性質。P4 は「1 周期の中で各 u64 が同じ回数ずつ出る」ことを示すので、P7 が成り立てば、1 周期の中で各 f32 が P7 の確率どおりの回数ずつ出ることが従う。ただし、P4 と P7 を両方示せるツールはない。

## 5. 横断的な論点

### 5.1 浮動小数点のサポート

**公式の位置づけ**

- **Kani:** CBMC が f32 をビット単位の IEEE 754 として扱うので、実行コードの演算をそのままたどれる。ただし実数の型がないので、実数との関係（丸め）や ±∞ になる条件は書けず、4.4 の f32 の add の仕様は書けない。また、既定では NaN を生む演算を誤りとして扱う（4.4 節）。
- **Creusot:** 保守者が「floating point numbers are currently mostly out of scope of Creusot」とコメントしている（[#2302](https://github.com/creusot-rs/creusot/issues/2302)）。
- **Verus:** ガイドで「Partially supported」とされ、vstd は浮動小数点の公理を意図的に省いている（`examples/float.rs`）。
- **Aeneas:** サポートしていない。
  - 保守者が「floats are not supported yet」とコメントしている（[AeneasVerif/aeneas#828](https://github.com/AeneasVerif/aeneas/issues/828)、open）。
  - 対応する PR は draft のまま（[#1073](https://github.com/AeneasVerif/aeneas/pull/1073)「Initial draft of basic float support for lean backend」）。
  - 変換器のソース（`src/extract/ExtractTypes.ml` 103〜107 行）に「Float, string, non-ASCII chars and byte string literals are unsupported」とある。Lean のライブラリにも `F32` / `F64` の型がない。
  - f32 を含む関数は、変換時にエラーになる（4.3 節・4.4 節）か、エラーなしで未定義の型 `F32` を参照する Lean が出力される（4.9 節）。

**既定の機能で書けるもの**

| | Kani | Creusot 0.14 | Verus 0.2026.11.02 | Aeneas |
|---|---|---|---|---|
| 実行コードの演算・比較 | IEEE 754 としてビット単位で正確 | IEEE 754 binary32・RNE として翻訳（保守者は保証していない） | 結果は未解釈関数（`add_ensures`、`lt_ensures` など） | 変換できない |
| 仕様での f32 の比較 | 使える（普通の Rust の式） | 使える（`<` / `>` / `<=` / `>=`） | 使える（`ieee_lt` など）が、実行コードの比較と結びつかない | － |
| NaN / ±∞ の判定 | 使える（`is_nan` など） | 仕様で使えず、コードから呼んでも検証できない | 使える（`ieee_is_nan` など）が、実行コードの演算結果について示せない | － |
| 仕様での f32 の演算 | 使える（普通の Rust の式） | 書けない（`Cannot add f32 to f32 in logic`） | 使える（`ieee_add` など。仕様の中では `by (bit_vector)` で証明できる）が、実行コードの演算と結びつかない | － |
| f32 の実数値・丸め | 書けない（実数の型がない） | 書けない（`Cannot take the view of f32`） | 使える（`as real` は丸めなし、`as f32` は RNE）が、実行コードの演算と結びつかない | － |
| 反例 | 出る | 出ない | 出ない | － |

**Creusot の Issue / PR**

`creusot-rs/creusot` の Issue・PR・Discussions を、`float`、`f32`、`f64`、`literal`、`Unsupported literal`、`NaN`、`floating` で検索した（2026-11-21）。今回見つけた次の 3 つの問題をそのまま扱っている Issue / PR は見つからなかった。

- 仕様中の f32 リテラルが内部エラーになること（4.3 節）
- 整数値の大きな float 定数が、不正確な 10 進数で Why3 に出力されること（4.4 節）
- 仕様で f32 の演算が使えないこと

関連するものは次のとおり。

- **[#2302](https://github.com/creusot-rs/creusot/issues/2302)（open）「Creusot doesn't fail wrong `Eq` trait impl」:** 保守者の jhjourdan 氏が「Indeed, floating point numbers are currently mostly out of scope of Creusot. It is not unsound, but it will refuse to verify anything that compare floats.」とコメントしている。
- **[#791](https://github.com/creusot-rs/creusot/issues/791)（closed）「Why3 IDE mlcfg error on small floats」:** `0.000001` が不正確な 10 進数で出力され、Why3 に拒否されるという報告。修正で、小数部のある値は正確な 16 進表記で出力されるようになった。整数値の分岐は 10 進出力のまま残っていて、`f32::MAX` 付近の問題はこの修正の対象外。
- **[#514](https://github.com/creusot-rs/creusot/pull/514)「Basic support for floats」:** 本文は「Adds very basic support for floats and their associated operations. I fully expect there to be holes」。
- **[#736](https://github.com/creusot-rs/creusot/pull/736)「Encode float operators with a dot」:** プログラム中の float の演算子を、Why3 の IEEE 演算子に翻訳する修正。
- **[#17](https://github.com/creusot-rs/creusot/issues/17)（closed）「Add polymorphic literals to pearlite」:** pearlite のリテラルの型推論についての Issue。float リテラルを翻訳しないことは扱っていない。

**Rust の f32 と Why3 の浮動小数点**

両者にずれはない。ただし、Rust の仕様が保証する範囲の中での話。

- **Rust の仕様:** RFC 3514（Float semantics）は、`+ - * / %`、`sqrt`、比較などが、NaN を除き「IEEE 754-2008 の結果と厳密に一致する（roundTiesToEven、トラップなし、flush-to-zero なし）」と定める。別の丸めモードでの実行はサポートせず、インラインアセンブリで浮動小数点の制御ビットを変えたまま戻るのは未定義動作。コンパイル時の定数評価も同じ仕様に従う。したがって、CPU やコンパイルの設定で丸めモードが変わることは、Rust の仕様の上では起きない。
- **Creusot の側:** prelude（`prelude-generator/float.coma`）は、f32 の演算を `Float32.add RNE a b` などと定義している。これは Rust の roundTiesToEven と同じ。Creusot が証明しているのは、「Rust の仕様どおりに IEEE 754 binary32・RNE で計算されるなら、仕様が成り立つ」こと。
- **注意点**（RFC 3514 が挙げる例外）:
  - NaN を生む演算の符号・ペイロードは非決定的。Why3 の `ieee_float.mlw`（153〜158 行）も、NaN の値が 1 つに定まることを仮定していない。
  - 32bit x86 で SSE2 がない場合（i586 など）は x87 レジスタが使われ、IEEE と異なる精度で計算されることがある。32bit ARM の NEON は flush-to-zero になる。こうしたターゲットでは Rust の仕様そのものが守られないので、Creusot の証明も成り立たない。Creusot がターゲットを考慮しているという記述は、ドキュメントにも実装にも見当たらない。

**Creusot で f32 の減算・乗算が仕様に書けない理由**

Why3 の制約ではなく、Creusot（creusot-std）側の制約。

- Why3 の `ieee_float` 理論には、f32 の加減乗除（丸めモード付き）、実数値 `to_real`、丸め `round` が揃っている。Creusot の prelude にも `creusot.float.Float32.add` / `sub` / `mul` / `div` の定義があり、プログラム中の演算はこれに翻訳される。
- 欠けているのは、仕様側の対応付け。pearlite の `+` / `-` / `*` は、creusot-std の `AddLogic` / `SubLogic` / `MulLogic` トレイトを通して Why3 の記号に対応付けられる。creusot-std は整数型にはこれらを実装しているが（`std/num.rs` 77〜96 行の `mach_int!` マクロ）、f32 には比較（`PartialOrdLogic`）しか実装していない。実数値が使えないのも同じ理由で、creusot-std は f32 のビューを提供していない。
- この欠落を追跡している Issue も見つからなかった。

### 5.2 事前条件と契約

#### 5.2.1 各ツールでの事前条件

- **Kani:** 関数に事前条件を付けて、呼び出し側に課す仕組みがない（関数の契約は不安定機能で、このリポジトリでは使わない）。ハーネスの `kani::assume` は、そのハーネスで調べる入力を絞るだけ。呼び出し側の誤りは、本体を実際にたどって失敗が起きたときにだけ見つかる（4.2 節）。
- **Creusot / Verus:** `requires` は関数の宣言に付き、本体の中身に関係なく、すべての呼び出し箇所で確かめられる。満たさない呼び出しは検証エラーになる。
- **Aeneas:** 次の 5.2.2 で述べる。

#### 5.2.2 Aeneas の事前条件

**仕様の書き方:** 関数の仕様は `@[step]` を付けた Lean の定理として書き、定理の仮定が事前条件になる。`@[step]` で登録した仕様は、呼び出し側の証明で `step` が使い、そのとき事前条件を呼び出し側で示す必要がある。

**仮定に書いただけの事前条件は強制されない:** 呼び出し側の定理は、どう証明してもよい。Lean では、呼び出し側の証明で関数の定義を展開することを禁止できない（`attribute [irreducible]` を付けても `unfold` と `simp [f]` は通り、止まるのは `rfl` だけだった）。そのため、事前条件を破る呼び出しでも、関数の実装がたまたま失敗しなければ、定義を展開して証明が通ってしまう。本体が空の関数に「事前条件 → 事後条件」の定理を付けた小さな例で、事前条件を確かめずに呼ぶ関数の定理が、定義の展開で証明できることを確かめた。

**事前条件を Rust の `assert!` / `debug_assert!` で書く:** Aeneas はこれを `massert`（条件が偽なら失敗する）に翻訳する。すると呼び出し側の定理は、本体の処理に関係なく、条件を示さないと証明できなくなる（4.2 節の `double`、4.14 節の `render_unvalidated`）。Aeneas による暗号ライブラリの検証（[arXiv 2609.15648](https://arxiv.org/abs/2609.15648)）も、5.5 節で「`assert!` を、引数が偽なら失敗する関数 `massert` に翻訳する。そのため、Rust の動的な表明はすべて、検証の一部として静的に示す必要がある」と書いている。このリポジトリでは、事前条件のある関数（02 の `add`、06 の `max`、13 の `mean`、14 の `process`）に `debug_assert!` を入れた。

**`debug_assert!` とビルドの種類:** `debug_assert!` はリリースビルドでは消え、条件も評価されない。Charon は `dev` プロファイルでビルドしたコードを翻訳するので、`debug_assert!` も `massert` になる（確かめた）。検査がデバッグビルドの実行時間に響く場合は、独自の `cfg` で、Charon の翻訳のときだけ検査を有効にできる。

```rust
pub fn min_of_sorted(v: &[u32]) -> u32 {
    #[cfg(verify)]
    assert!(is_sorted(v));
    v[0]
}
```

- 通常のビルド（デバッグを含む）では、この `assert!` は消える。
- `RUSTFLAGS="--cfg verify" charon cargo --preset=aeneas` で翻訳すると、`let b ← is_sorted v; massert b` が入ることを確かめた。
- `cfg(verify)` を `Cargo.toml` の `[lints.rust] unexpected_cfgs` の `check-cfg` に足しておけば、警告は出ない。

**この方法の制約:** 事前条件を、Rust の実行可能なコードとして書く必要がある。さらに、そのコードは Aeneas が翻訳できる範囲のものでなければならない（4.14 節で `Result::is_ok` を `matches!` に書き換えたのは、`is_ok` が中身のない axiom になるため）。Rust で計算できない条件は、この方法では事前条件にできない（5.2.4 節）。

#### 5.2.3 Aeneas の検証で保証されることと信用すること

暗号ライブラリの検証論文（arXiv 2609.15648）の 3 節「Trust Assumptions」は、次のように分けている。

- **Lean が検査するので、信用しなくてよいもの:** 証明、および内部の補助関数に付けた性質と中間の仕様（「systematically checked by Lean」）。
- **信用するもの:**
  - 規格を表す Lean の仕様が、規格を正しく表していること（人間のレビューとテストで確かめる）。
  - 公開 API の事前条件・事後条件が、意図した振る舞いを過不足なく表していること（Lean の定理を読んでレビューできる）。
  - axiom にした標準ライブラリと CPU 命令のモデル（ベンダーの資料と照合してレビューする）。
  - Rust のツールチェイン、Charon・Aeneas の翻訳、Lean のカーネル。
  - 検証済みの実装を使う外部のコードが、安全で、事前条件を守ること（「We also trust that code using our verified implementations is safe, complies with its pre-conditions」）。

つまり保証されるのは、「公開 API を、その事前条件を満たす引数で呼べば、パニックせずに、事後条件を満たす値を返す」ことである。公開 API の外側の呼び出し元は検証の対象外で、そこが事前条件を守ることは信用している。8.1 節は、AI が「ずるい仮定や弱めたゴール」を使おうとするので、定理の記述の人間によるレビューが不可欠だとしている。

内部の関数の事前条件が呼び出し側で守られることを強制する仕組みは、論文には書かれていない。保証の対象が公開 API の定理なので、内部の関数の事前条件は、公開 API の定理を証明するときに使われる範囲でだけ意味を持つ。内部の関数の契約そのものを検証したい場合は、5.2.2 節の `assert!` / `debug_assert!` の方法で、契約をコードの意味に入れる必要がある。

#### 5.2.4 Rust のコードで書けない事前条件

Creusot と Verus の事前条件は仕様の言語で書くので、実行しても確かめられない条件も書ける。Aeneas の `assert!` の方法では、事前条件を Rust の実行可能なコードとして書く必要がある。

量化（「すべての〜について」）を含む条件でも、範囲が実行時に数え上げられるもの（スライスの全要素、添字の範囲など）なら、Rust のループで検査関数を書ける。書けないのは、次のような条件である。

| 種類 | 例 | Aeneas の `assert!` で書けない理由 |
|---|---|---|
| 任意の型の値についての法則 | 4.12 節の結合律「任意の `a`, `b`, `c` で `op(op(a, b), c) = op(a, op(b, c))`」 | 任意の型 `T` の値は数え上げられない。また、`T` に等しさがあるとは限らず、あっても値の等しさとは限らないので、Rust では「等しい」を確かめられない |
| クロージャの仕様 | 13 の `join` の事前条件（Verus の `a.requires(())`、Creusot の `a.precondition(())`） | Rust のクロージャは、実行時に自分の仕様を持たない |
| ゴーストの権限・状態 | 05 の `PointsTo` / `Perm`（「このポインタが指すメモリを所有している」）、10 のトークン | ポインタが有効なメモリを指すかは、実行時に調べられない（Aeneas はそもそも unsafe と並行処理に非対応） |

任意の型の値についての法則は、4.12 節の `fold_halves` の事前条件にあたる。Aeneas では `assert!` で書けず、定理の仮定にしても、定義を展開できるので呼び出し側に課されない。一方、4.13 節の `par_sum` のように本体を翻訳せず axiom で信用する関数なら、使える事実が axiom だけなので、axiom の仮定は呼び出し側に課される。

数え上げられる条件でも、範囲が大きいと検査関数を実際には実行できない（例 2）。

**例 1: 配列の全要素についての条件（Aeneas でも書ける）**

「整列済みの配列の最小値は先頭」という関数で確かめた（確かめたあと削除した）。

```rust
pub fn is_sorted(v: &[u32]) -> bool {
    let mut i = 1;
    while i < v.len() {
        if v[i - 1] > v[i] {
            return false;
        }
        i += 1;
    }
    true
}

pub fn min_of_sorted(v: &[u32]) -> u32 {
    debug_assert!(is_sorted(v));
    v[0]
}
```

- Verus では、`requires forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j]` と書けば、本体 1 行のまま検証が通り、整列済みと分からない配列で呼ぶ関数は `precondition not satisfied` で弾かれる。
- Aeneas では、`debug_assert!` の部分が「関数の先頭で `is_sorted` を 1 回呼び、その結果を `massert` する」形に翻訳される。`min_of_sorted` の証明には、検査関数 `is_sorted` のループの仕様と、仕様の「整列済み」（任意の `i < j`）から検査の「隣どうし」を導く部分が要る。整列済みであることは呼び出し側でも示す必要があるので、Verus との違いは、検査関数を一度検証する分だけになる。
- デバッグビルドでは呼ぶたびに配列全体を走査する。要素数 100 万の配列で 1,000 回呼ぶと、`debug_assert!` ありで 1.25 秒、`-C debug-assertions=off` で 4.91 µs、リリースビルドで 70 ns だった。5.2.2 節の `cfg` の方法を使えば、この実行時間は避けられる。
- したがって、配列の要素のように数え上げられる範囲の条件は、Aeneas でも事前条件として書ける。

**例 2: u64 のすべての値についての条件（Aeneas でも書けるが、検査関数を実行できないので `cfg(verify)` で外す）**

述語 `P::test` が真になる最小の u64 を、二分探索で求める関数で確かめた（確かめたあと削除した）。

```rust
pub trait Pred {
    fn test(x: u64) -> bool;
}

#[cfg(verify)]
fn is_monotone<P: Pred>() -> bool {
    let mut x: u64 = 0;
    while x < u64::MAX {
        if P::test(x) && !P::test(x + 1) {
            return false;
        }
        x += 1;
    }
    true
}

pub fn first_true<P: Pred>() -> u64 {
    #[cfg(verify)]
    assert!(is_monotone::<P>() && P::test(u64::MAX));
    let mut lo: u64 = 0;
    let mut hi: u64 = u64::MAX;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if P::test(mid) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    lo
}
```

- **関数の仕様:** 事前条件は「`test` が単調（`x <= y` で `test(x)` が真なら `test(y)` も真）」かつ「`test(u64::MAX)` が真」。事後条件は「`test(r)` が真で、`r` より小さいどの `y` でも `test(y)` が偽」。
- **単調性は、呼び出しのたびに引数を調べる形では確かめられない。** 二分探索が調べるのは 64 点ほどで、その外で単調性が破れていても結果は誤る。単調性は、u64 のすべての値についての条件である。
- **インスタンス:** 単調な `AtLeast100`（`x >= 100`）と、単調でない `Even`（`x % 2 == 0`）を用意し、`first_at_least_100` と `first_even` でそれぞれ `first_true` を呼んだ。

確かめた結果:

- **Verus:** 事前条件を量化子でそのまま書ける。

  ```rust
  pub fn first_true<P: Pred>() -> (r: u64)
      requires
          forall|x: u64, y: u64| x <= y && #[trigger] P::test_spec(x) ==> #[trigger] P::test_spec(y),
          P::test_spec(u64::MAX),
      ensures
          P::test_spec(r),
          forall|y: u64| y < r ==> !#[trigger] P::test_spec(y),
  ```

  トレイトに `spec fn test_spec` を置き、`test` の事後条件を `r == Self::test_spec(x)` とした。`first_at_least_100`（事後条件 `r == 100`）は、量化子のトリガーを与える `assert(AtLeast100::test_spec(100))` を足して検証が通った。`first_even` だけが `precondition not satisfied`（単調性の行）で弾かれた（`verification results:: 5 verified, 1 errors`）。
- **Aeneas:** 単調性を確かめる検査関数 `is_monotone` は、u64 の隣り合う値の組をすべて調べる。実行すると 2⁶⁴ 回近いループになり、1 回 1 ns としても約 580 年かかる。そのため `debug_assert!` には使えない（デバッグビルドの呼び出しが終わらない）。`#[cfg(verify)]` で、すべてのビルドから外した。
  - `RUSTFLAGS="--cfg verify" charon cargo --preset=aeneas` で翻訳すると、`first_true` の先頭は次のようになった。`&&` で結んだ `assert!` は、2 つの `massert` に分かれる。

    ```lean
    def first_true {P : Type _} (PredInst : Pred P) : Result Std.U64 := do
      let b ← is_monotone PredInst
      massert b
      let b1 ← PredInst.test core.num.U64.MAX
      massert b1
      first_true_loop PredInst 0#u64 core.num.U64.MAX
    ```

  - 証明した定理は次のとおり。`p` は `test` を表す純粋な関数。

    ```lean
    theorem is_monotone_loop_spec {P : Type} (inst : Pred P) (p : U64 → Bool)
        (htest : ∀ x, inst.test x ⦃ r => r = p x ⦄) (x : U64) :
        is_monotone_loop inst x ⦃ r => r = true ↔
          ∀ y z : U64, x.val ≤ y.val → z.val = y.val + 1 → p y → p z ⦄

    theorem first_true_spec {P : Type} (inst : Pred P) (p : U64 → Bool)
        (htest : ∀ x, inst.test x ⦃ r => r = p x ⦄)
        (hmono : ∀ y z : U64, y.val ≤ z.val → p y → p z) (hmax : p core.num.U64.MAX) :
        first_true inst ⦃ r => p r ∧ ∀ y : U64, y.val < r.val → ¬ p y ⦄

    theorem first_at_least_100_spec : first_at_least_100 ⦃ r => r.val = 100 ⦄
    ```

  - **証明は現実的な時間で終わる。** 検査関数のループは、帰納法（`termination_by U64.max - x.val`）で 1 回示せばよく、Lean が 2⁶⁴ 個の値を 1 つずつ調べるわけではない。二分探索のループの仕様と `first_true_spec` は `step*` だけで通った。証明を含む `Properties.lean` のビルドは約 1.4 秒だった。
  - **単調でない述語での呼び出しは拒否される。** `first_even` について、`first_true_spec` の仮定 `hmono` と `hmax` は示せない。定義を展開して `first_even ⦃ _ => True ⦄`（失敗しない）を直接示そうとしても、`massert` の条件 `b = true`（`b` は `is_monotone` の結果）がゴールに残る。`is_monotone_loop_spec` から、これは `Even` が単調であることと同値で、偽である。
- **Verus・Creusot との違い:** Verus・Creusot では、条件を仕様として書き、実行コードには何も残らない。Aeneas でも書けて、呼び出し側にも強制できる。ただしそのために、決して実行しない検査関数を Rust で書き、`cfg` で外し、そのループの仕様も証明する必要がある。

### 5.3 外部のコードを信用する方法

| ツール | 方法 | 信用する内容 |
|---|---|---|
| Kani | 関数スタブ（`#[kani::stub]`、不安定機能） | 代わりの実装（逐次版など）。その実装を実行して調べる |
| Creusot | `#[trusted]` | 宣言した `requires` / `ensures` |
| Verus | `#[verifier::external_body]` | 宣言した `requires` / `ensures` |
| Aeneas | Charon の `--opaque` で本体を外し、Lean の `axiom` で性質を書く | axiom として書いた性質 |

### 5.4 性質を型で表すか、述語で表すか

14 では、「仕様の規則を満たす」という性質を、`Gltf` を包む新しい型（Verus の `#[verifier::type_invariant]` などを使うもの）ではなく、`Gltf` 上の述語 `valid` として表し、事前条件・事後条件で受け渡した。

- **包む型の方式の問題:** 性質 A と B をそれぞれ型で表すと、A の型、B の型、A かつ B の型が要り、性質の組み合わせごとに型が増える。包む順序で `A<B<T>>` と `B<A<T>>` が別の型になり、両者が同じものだという関係も、「A かつ B の型は A の型の部分集合」という包含関係も、型では表せない。
- **Verus の型の不変条件:** ガイドの `reference-type-invariants.md` によると、主な用途は「不変条件のカプセル化と隠蔽」で、1 つの構造体・列挙型に 1 つの述語を付ける。付けられるのは、同じクレートで宣言され、フィールドがクレート外に公開されていない型に限る。部分型（refinement type）や型どうしの包含関係もない（`reference-types.md`）。したがって、同じ型に複数の性質を組み合わせて付け、その包含関係を型で扱うことは、Verus ではできない。
- **Creusot の型の不変条件:** `Invariant` トレイトで型ごとに 1 つの述語を与える仕組みで、性質の組み合わせを型で扱う仕組みはない。
- **述語の方式:** 性質が増えても連言で組み合わせられる（14 の `valid` は、参照の範囲・対応範囲・ノードの木・メッシュ・スキン・アニメーション・bufferView・アクセサー・バッファー・画像・カメラなどの規則の連言）。`A && B` から `A` が導けることもソルバー（Aeneas では Lean の証明）が扱う。その代わり、性質は型に残らないので、値を渡す関数ごとに事前条件に書き、呼び出し側で示す必要がある。

## 6. まとめ

- **Kani**
  - 普通の Rust（unsafe、浮動小数点、標準ライブラリの実装）を、そのままビット単位で正確に調べられ、反例も出る。
  - ループは展開できる回数まで、型は具体的な型だけ、スレッドは非対応。「すべての入力について」の証明や、証明の誘導はできない。
  - 安定した機能では、関数に契約を付けて呼び出し側に課すことはできず（関数の契約は不安定機能で、このリポジトリでは使わない）、本体を実際にたどって失敗を見つける。
  - 汎用の関数を検証できず、事前条件も課せないので、法則を満たさない型で `fold_halves` を呼んでも拒否されない（4.12 節）。外部の関数は、仕様を宣言して信用するのではなく、スタブで実装を差し替える（4.13 節）。
  - 浮動小数点をビット単位で正確に扱えるので、u64 から [0, 1) の f32 への変換が NaN・±∞ を返さず、[0, 1) に収まることを確かめられた。一方、確率（入力の個数）は書けないので一様性は書けず、PCG の周期のように 2^128 回の繰り返しについての性質も書けない（4.15 節）。
- **Creusot**
  - 仕様を属性マクロで書くので、コードは普通の Rust のまま。`&mut` を prophecy（`^`）で扱う。
  - トレイトに法則（`#[logic(law)]`）を置き、実装ごとに証明させられる。法則は使う側の証明に自動で入る（4.12 節）。
  - Why3 経由で複数のプルーバを使う。
  - `Vec` を介した再帰型と、関数（論理関数を含む）の相互再帰が使えない。JSON の木のような再帰的なデータと、相互再帰する再帰下降パーサーは、そのままでは書けない（4.14 節）。
  - 既定は部分正当性で、停止性は `#[check(terminates)]` を付けた関数でだけ証明される（4.14 節）。
  - 浮動小数点は公式には「ほぼ対象外」で、仕様で使えるのは f32 の比較だけ。仕様の中の f32 リテラル、float 定数の Why3 への出力、`#[derive(DeepModel)]` の通常ビルドなど、細部に未成熟な点がある。ガイドにまだ説明のない機能（DeepModel など）もある。
- **Verus**
  - 独自の構文（`verus!` の中の `requires` / `ensures` / `returns` / `spec` / `proof`）を使う。ゴースト状態（`Tracked`）、状態機械、型の不変条件など、システムプログラミング向けの道具が最も揃っている。
  - トレイトに `proof fn` で法則を置き、実装ごとに証明させられる（4.12 節）。
  - エラーの表示が rustc と同じ形式で分かりやすい。
  - SMT への問い合わせを小さく保つ設計で、補助を明示的に書く場面が多い（非線形算術は既定で無効、ループは前の事実を引き継がない、opaque な定義は `reveal` が要る）。
  - 仕様を書いて証明する過程で、実際のバグ（i32 の推論によるオーバーフロー）を見つけた（4.14 節）。
  - スレッドの `join` の失敗を除外できないので、「`join` が成功すれば」という条件付きの仕様になる。
  - 浮動小数点は、意図的にほぼ対象外。仕様の側には IEEE の演算・比較と実数への変換があるが、実行コードの演算と結びついていない（4.3 節・4.4 節・4.15 節）。
- **Aeneas**
  - 安全な Rust の部分集合を Lean の関数に翻訳し、性質は別ファイルの Lean の定理として書いて tactic で証明する。`&mut` は「新しい値を返す」関数に変わるので、prophecy も分離論理も要らない。
  - 自動化は `step*` と `agrind` が中心で、SMT ソルバーは使わない。補題、帰納法、存在を示す値は自分で与える。Lean と Mathlib の道具をすべて使える。
  - 関数の仕様は `@[step]` 定理として書く。事前条件を定理の仮定に書くだけでは呼び出し側に強制できないので、契約として強制するには、事前条件を Rust の `assert!` / `debug_assert!` で書く。
  - この方法で書けるのは Rust で計算できる条件だけで、「任意の型の値についての法則」は書けない。そのため、4.12 の `fold_halves` のように、そうした法則を事前条件に持つ関数は書けない（定理の仮定にしても、呼び出し側に課されない）。
  - 本体を翻訳せず axiom で信用する関数は、axiom の仮定が呼び出し側に課されるので、法則を事前条件に持つ仕様も信用できる（4.13 節）。
  - u64 のすべての値のように数え上げられるが範囲が大きい条件は、実行できない検査関数を Rust で書き、`cfg(verify)` で通常のビルドから外し、そのループも証明することになる（5.2.4 節の例 2）。
  - 浮動小数点、unsafe（生ポインタ）、並行処理は非対応。README では、unsafe と並行処理は分離論理の作業で今後対応するとしている。浮動小数点は、エラーにならずに壊れた Lean が出る場合もある。
  - 標準ライブラリや外部クレートの関数は、Aeneas の Lean ライブラリにモデルがあればそれを使い、なければ中身のない axiom になる。
  - 翻訳できる Rust の書き方に制限がある（return を含むループのあとに処理が続く書き方、`Option` の `==` など）。大きな関数では、Charon が数十 GB のメモリを使って止まることがある。実用規模のコードでは、これらを避ける形に書き直す必要があった（4.14 節）。
  - `Vec::push` は長さが上限を超えると失敗するというモデルで、Verus と Creusot のモデルはこの上限を含まない。そのため、14 では「値の木のノード数が上限以下」を示す必要があった（4.14 節）。
  - 導入は最も重い。OCaml（opam）、Rust（rustup）、Lean（elan）の 3 つの環境が要る。Lean のプロジェクトごとに Mathlib を含む `.lake/` が必要で、既定では 1 つあたり約 7.4GB になる。Lake の成果物キャッシュで共有できる（10 プロジェクトで合計約 5.7GB）。

## 付録 A. glTF 2.0 の MUST の一覧（14 の検証との対応）

glTF 2.0 の仕様書の原稿（KhronosGroup/glTF の `specification/2.0/Specification.adoc`、main ブランチ）から、**MUST**・**MUST NOT**・**REQUIRED** を含む文を取り出した 162 文。番号は 14 のコード中のコメント（`// MUST-016` など）と対応する。「行」は原稿の行番号、「節」は文がある節。

- 検証した: 107 文。「検査する関数」は 3 ツール共通のコードの関数（モジュール::関数）。
- 検査しない（中身）: 37 文。バッファー・画像のバイナリのデータの中身が要る（外部ファイルは読まない）。
- 検査しない（浮動小数点）: 9 文。浮動小数点の値の比較が要る。
- 対象外（クライアント）: 4 文。描画するクライアントの振る舞いで、文書の性質ではない。
- 対象外（仕様書）: 4 文。用語の定義と、仕様書の改訂についての約束。
- 対象外（拡張の意味）: 1 文。どの拡張が読み込みに必要かは、拡張の意味による（このローダーは `extensionsRequired` が空でなければ `Unsupported` を返す）。

| 番号 | 行 | 節 | 内容 | 分類 | 検査する関数 |
|---|---|---|---|---|---|
| MUST-001 | 86 | Document Conventions > Normative Terminology and References | 用語の定義 | 対象外（仕様書） | － |
| MUST-002 | 385 | glTF Basics | version が必要 | 検証した | `read::read_gltf` |
| MUST-003 | 392 | Versioning | 仕様書の改訂の約束 | 対象外（仕様書） | － |
| MUST-004 | 400 | Versioning | 仕様書の改訂の約束 | 対象外（仕様書） | － |
| MUST-005 | 400 | Versioning | 仕様書の改訂の約束 | 対象外（仕様書） | － |
| MUST-006 | 473 | JSON Encoding | 整数のプロパティは小数部が 0 | 検証した | `json::number::number_to_u64` |
| MUST-007 | 520 | URIs > Data URLs | data URL のメディアタイプと中身の一致 | 検査しない（中身） | － |
| MUST-008 | 622 | Asset | asset が必要 | 検証した | `read::read_gltf` |
| MUST-009 | 624 | Asset | asset.version が必要 | 検証した | `read::read_gltf` |
| MUST-010 | 626 | Asset | version / minVersion の構文 | 検証した | `read::objects::parse_version` |
| MUST-011 | 662 | Asset | クライアントは minVersion に対応しなければ読み込めない（ローダーの振る舞い） | 検証した | `validate::support::supported` |
| MUST-012 | 662 | Asset | minVersion ≤ version | 検証した | `validate::asset_ok` |
| MUST-013 | 723 | Indices and Names | インデックスは 0 以上の整数 | 検証した | `json::number::number_to_u64`, `read::access::get_uint` |
| MUST-014 | 723 | Indices and Names | インデックスは範囲内 | 検証した | `validate::refs::refs_in_range` |
| MUST-015 | 769 | Scenes > Overview | scene.nodes は重複なし | 検証した | `validate::hierarchy::scenes_ok` |
| MUST-016 | 810 | Scenes > Nodes and Hierarchy | ノードの階層は互いに素な木 | 検証した | `validate::hierarchy::parents`, `node_ok (root_of)` |
| MUST-017 | 810 | Scenes > Nodes and Hierarchy | 循環なし・親は 0 か 1 | 検証した | `validate::hierarchy::parents`, `node_ok (root_of)` |
| MUST-018 | 812 | Scenes > Nodes and Hierarchy | children は重複なし | 検証した | `validate::hierarchy::node_ok` |
| MUST-019 | 865 | Scenes > Transformations | rotation は単位四元数 | 検査しない（浮動小数点） | － |
| MUST-020 | 881 | Scenes > Transformations | matrix は TRS に分解できる | 検査しない（浮動小数点） | － |
| MUST-021 | 1012 | Buffers > Overview | 参照先の長さ ≥ byteLength（data URL は検証。外部ファイルは読まない） | 検証した | `validate::resource::buffer_uri_ok`, `validate::resource::buffer_ok` |
| MUST-022 | 1014 | Buffers > Overview | バッファーの data URL のメディアタイプ | 検証した | `validate::resource::buffer_media_type_ok` |
| MUST-023 | 1023 | Buffers > GLB-stored Buffer | GLB のバッファー 0（uri なし）には BIN チャンクが必要 | 検証した | `validate::resource::buffer_ok` |
| MUST-024 | 1048 | Buffers > GLB-stored Buffer | BIN チャンク ≥ バッファーの byteLength | 検証した | `validate::resource::buffer_ok` |
| MUST-025 | 1095 | Buffer Views > Overview | bufferView はバッファーに収まる | 検証した | `validate::data::buffer_view_ok` |
| MUST-026 | 1097 | Buffer Views > Overview | bufferView は 1 種類のデータだけ | 検証した | `validate::data::buffer_view_ok`, `view_use` |
| MUST-027 | 1099 | Buffer Views > Overview | 画像の bufferView はアクセサーから使わない | 検証した | `validate::data::buffer_view_ok`, `view_use` |
| MUST-028 | 1101 | Buffer Views > Overview | 他の種類のデータの bufferView は target を持たない | 検証した | `validate::data::target_ok` |
| MUST-029 | 1109 | Buffer Views > Overview | 2 つ以上の頂点属性が使う bufferView は byteStride が必要 | 検証した | `validate::data::stride_ok` |
| MUST-030 | 1109 | Buffer Views > Overview | 他の種類のデータの bufferView は byteStride を持たない | 検証した | `validate::data::stride_ok` |
| MUST-031 | 1113 | Buffer Views > Overview | byteStride は 4 の倍数 | 検証した | `validate::data::stride_ok` |
| MUST-032 | 1114 | Buffer Views > Overview | 4 ≤ byteStride ≤ 252 | 検証した | `validate::data::stride_ok` |
| MUST-033 | 1115 | Buffer Views > Overview | byteStride ≤ byteLength | 検証した | `validate::data::stride_ok` |
| MUST-034 | 1131 | Accessors > Overview | bufferView がなければ byteOffset もない | 検証した | `validate::data::accessor_view_ok` |
| MUST-035 | 1197 | Accessors > Accessor Data Types | 5125/5126 は normalized にしない | 検証した | `validate::data::accessor_ok` |
| MUST-036 | 1321 | Accessors > Accessing Data from Buffer Views | アクセサーは bufferView に収まる | 検証した | `validate::data::accessor_view_ok (fits)` |
| MUST-037 | 1328 | Accessors > Accessing Data from Buffer Views | オフセットは成分の大きさの倍数 | 検証した | `validate::data::accessor_view_ok` |
| MUST-038 | 1336 | Accessors > Accessing Data from Buffer Views | 頂点属性以外のアクセサーはストライド付きの bufferView を使わない | 検証した | `validate::data::stride_ok`, `view_use` |
| MUST-039 | 1336 | Accessors > Accessing Data from Buffer Views | 2 つ以上の頂点属性アクセサー（モーフを含む）が使う bufferView は byteStride が必要 | 検証した | `validate::data::stride_ok`, `view_use` |
| MUST-040 | 1340 | Accessors > Accessing Data from Buffer Views | byteStride ≥ 要素の大きさ | 検証した | `validate::data::accessor_view_ok` |
| MUST-041 | 1348 | Accessors > Accessing Data from Buffer Views | byteStride は成分の大きさの倍数 | 検証した | `validate::data::accessor_view_ok` |
| MUST-042 | 1356 | Accessors > Accessing Data from Buffer Views | 頂点属性の要素は 4 バイト境界 | 検証した | `validate::data::accessor_view_ok` |
| MUST-043 | 1408 | Sparse Accessors > Overview | sparse の必須プロパティ | 検証した | `read::objects::read_sparse` |
| MUST-044 | 1410 | Sparse Accessors > Overview | 0 < sparse.count ≤ count | 検証した | `validate::data::sparse_ok` |
| MUST-045 | 1452 | Sparse Accessors > Sparse Accessor Indices | sparse のインデックスは符号なし整数型 | 検証した | `validate::data::sparse_ok` |
| MUST-046 | 1454 | Sparse Accessors > Sparse Accessor Indices | sparse.indices の bufferView は byteStride / target なし | 検証した | `validate::data::stride_ok`, `target_ok`, `view_use` |
| MUST-047 | 1464 | Sparse Accessors > Sparse Accessor Indices | sparse.indices のオフセットの境界 | 検証した | `validate::data::sparse_ok` |
| MUST-048 | 1473 | Sparse Accessors > Sparse Accessor Indices | sparse.indices は bufferView に収まる | 検証した | `validate::data::sparse_ok` |
| MUST-049 | 1480 | Sparse Accessors > Sparse Accessor Indices | sparse のインデックスは昇順で count 未満 | 検査しない（中身） | － |
| MUST-050 | 1485 | Sparse Accessors > Sparse Accessor Values | sparse.values の bufferView は byteStride / target なし | 検証した | `validate::data::stride_ok`, `target_ok`, `view_use` |
| MUST-051 | 1495 | Sparse Accessors > Sparse Accessor Values | sparse.values のオフセットの境界 | 検証した | `validate::data::sparse_ok` |
| MUST-052 | 1504 | Sparse Accessors > Sparse Accessor Values | sparse.values は bufferView に収まる | 検証した | `validate::data::sparse_ok` |
| MUST-053 | 1530 | Accessors > Accessor Bounds | min / max の長さ = 成分数 | 検証した | `validate::data::accessor_ok (bounds_len_ok)` |
| MUST-054 | 1532 | Accessors > Accessor Bounds | min / max と実データの一致（整数） | 検査しない（中身） | － |
| MUST-055 | 1534 | Accessors > Accessor Bounds | min / max と実データの一致（正規化整数） | 検査しない（中身） | － |
| MUST-056 | 1536 | Accessors > Accessor Bounds | min / max と実データの一致（浮動小数点） | 検査しない（浮動小数点） | － |
| MUST-057 | 1558 | Accessors > Accessor Bounds | POSITION とアニメーションの入力は min / max が必要 | 検証した | `validate::mesh::attribute_ok`, `validate::animation::animation_samplers_ok` |
| MUST-058 | 1626 | Meshes > Vertex Attributes | attributes は平らな「名前 → アクセサー」 | 検証した | `read::objects::read_attribute_map` |
| MUST-059 | 1637 | Meshes > Vertex Attributes | 属性の型の表 | 検証した | `validate::mesh::attribute_type_ok` |
| MUST-060 | 1667 | Meshes > Vertex Attributes | 集合の番号は 0 以上の 10 進整数 | 検証した | `validate::mesh::parse_set_index` |
| MUST-061 | 1668 | Meshes > Vertex Attributes | 集合の番号は先頭に 0 を付けない | 検証した | `validate::mesh::parse_set_index` |
| MUST-062 | 1669 | Meshes > Vertex Attributes | 集合の番号は 9 桁以下 | 検証した | `validate::mesh::parse_set_index` |
| MUST-063 | 1676 | Meshes > Vertex Attributes | TEXCOORD_ などの後ろは正しい番号 | 検証した | `validate::mesh::semantic`, `attribute_ok` |
| MUST-064 | 1678 | Meshes > Vertex Attributes | 集合の番号に欠けがない | 検証した | `validate::mesh::attribute_ok` |
| MUST-065 | 1687 | Meshes > Vertex Attributes | 属性データに無限大・NaN がない | 検査しない（中身） | － |
| MUST-066 | 1689 | Meshes > Vertex Attributes | POSITION は min / max が必要 | 検証した | `validate::mesh::attribute_ok` |
| MUST-067 | 1691 | Meshes > Vertex Attributes | TANGENT の w は ±1 | 検査しない（中身） | － |
| MUST-068 | 1693 | Meshes > Vertex Attributes | COLOR_0 は [0, 1] | 検査しない（中身） | － |
| MUST-069 | 1695 | Meshes > Vertex Attributes | 属性の要素数が等しい | 検証した | `validate::mesh::attribute_ok` |
| MUST-070 | 1697 | Meshes > Vertex Attributes | 属性の bufferView の target は頂点配列 | 検証した | `validate::data::target_ok` |
| MUST-071 | 1726 | Meshes > Topology and Connectivity | インデックスのアクセサーは SCALAR で符号なし整数 | 検証した | `validate::mesh::index_accessor_ok` |
| MUST-072 | 1726 | Meshes > Topology and Connectivity | インデックスの bufferView は byteStride なし、target は要素配列 | 検証した | `validate::data::stride_ok`, `target_ok` |
| MUST-073 | 1728 | Meshes > Topology and Connectivity | インデックスの値 < 頂点数 | 検査しない（中身） | － |
| MUST-074 | 1730 | Meshes > Topology and Connectivity | インデックスに最大値がない | 検査しない（中身） | － |
| MUST-075 | 1738 | Meshes > Topology and Connectivity | 頂点数は正 | 検証した | `validate::mesh::vertex_count_ok` |
| MUST-076 | 1750 | Meshes > Topology and Connectivity | ライン・ループの頂点数 ≥ 2 | 検証した | `validate::mesh::vertex_count_ok` |
| MUST-077 | 1758 | Meshes > Topology and Connectivity | ライン・ストリップの頂点数 ≥ 2 | 検証した | `validate::mesh::vertex_count_ok` |
| MUST-078 | 1764 | Meshes > Topology and Connectivity | ラインの頂点数は 2 の倍数 | 検証した | `validate::mesh::vertex_count_ok` |
| MUST-079 | 1772 | Meshes > Topology and Connectivity | 三角形の頂点数は 3 の倍数 | 検証した | `validate::mesh::vertex_count_ok` |
| MUST-080 | 1780 | Meshes > Topology and Connectivity | 三角形ストリップの頂点数 ≥ 3 | 検証した | `validate::mesh::vertex_count_ok` |
| MUST-081 | 1788 | Meshes > Topology and Connectivity | 三角形ファンの頂点数 ≥ 3 | 検証した | `validate::mesh::vertex_count_ok` |
| MUST-082 | 1832 | Morph Targets > Overview | targets の要素は平らな「名前 → アクセサー」 | 検証した | `read::objects::read_attribute_map` |
| MUST-083 | 1834 | Morph Targets > Overview | モーフターゲットの名前は attributes にある | 検証した | `validate::mesh::attribute_ok` |
| MUST-084 | 1844 | Morph Targets > Overview | メッシュ内のモーフターゲットの数は等しい | 検証した | `validate::mesh::primitive_ok` |
| MUST-085 | 1854 | Morph Targets > Overview | mesh.weights の長さ = モーフターゲットの数 | 検証した | `validate::mesh::mesh_ok` |
| MUST-086 | 1914 | Morph Targets > Difference Data Storage | モーフターゲットの属性の型の表 | 検証した | `validate::mesh::attribute_type_ok` |
| MUST-087 | 1941 | Morph Targets > Difference Data Storage | モーフのデータに無限大・NaN がない | 検査しない（中身） | － |
| MUST-088 | 1943 | Morph Targets > Difference Data Storage | モーフの POSITION は min / max が必要 | 検証した | `validate::mesh::attribute_ok` |
| MUST-089 | 1947 | Morph Targets > Difference Data Storage | モーフの要素数 = 属性の要素数 | 検証した | `validate::mesh::attribute_ok` |
| MUST-090 | 1949 | Morph Targets > Difference Data Storage | モーフの bufferView の target は頂点配列 | 検証した | `validate::data::target_ok` |
| MUST-091 | 2011 | Meshes > Skinned Mesh Primitive Attributes | JOINTS_n と WEIGHTS_n は対で存在 | 検証した | `validate::mesh::attribute_ok` |
| MUST-092 | 2021 | Meshes > Skinned Mesh Primitive Attributes | WEIGHTS は 0 以上 | 検査しない（中身） | － |
| MUST-093 | 2023 | Meshes > Skinned Mesh Primitive Attributes | 重み付きの関節は頂点ごとに重複なし | 検査しない（中身） | － |
| MUST-094 | 2048 | Meshes > Skinned Mesh Primitive Attributes | 正規化整数の重みの和は 1 | 検査しない（中身） | － |
| MUST-095 | 2088 | Skins > Overview | skin.joints が必要 | 検証した | `read::objects::read_skin` |
| MUST-096 | 2090 | Skins > Overview | joints は重複なし | 検証した | `validate::hierarchy::skin_ok` |
| MUST-097 | 2114 | Skins > Overview | 逆バインド行列のアクセサーの型と要素数 | 検証した | `validate::hierarchy::skin_ok` |
| MUST-098 | 2114 | Skins > Overview | 逆バインド行列の bufferView は byteStride / target なし | 検証した | `validate::data::stride_ok`, `target_ok` |
| MUST-099 | 2116 | Skins > Overview | 逆バインド行列の値と 4 行目 | 検査しない（中身） | － |
| MUST-100 | 2124 | Skins > Overview | skeleton は全関節の根か共通の祖先 | 検証した | `validate::hierarchy::joints_ok` |
| MUST-101 | 2137 | Skins > Joint Hierarchy | 関節には共通の祖先がある | 検証した | `validate::hierarchy::joints_ok` |
| MUST-102 | 2204 | Instantiation > Morph Targets | node.weights の長さ = モーフターゲットの数 | 検証した | `validate::hierarchy::node_ok` |
| MUST-103 | 2233 | Instantiation > Skinned Mesh Primitives | skin があれば mesh も必要 | 検証した | `validate::hierarchy::node_ok` |
| MUST-104 | 2233 | Instantiation > Skinned Mesh Primitives | スキンのメッシュのプリミティブは JOINTS_n と WEIGHTS_n を持つ | 検証した | `validate::hierarchy::skinned_mesh_ok (JOINTS_0 と対の規則 091)` |
| MUST-105 | 2235 | Instantiation > Skinned Mesh Primitives | スキンの関節の共通の祖先は同じシーンに属する | 検証した | `validate::hierarchy::skin_scene_ok` |
| MUST-106 | 2242 | Instantiation > Skinned Mesh Primitives | JOINTS の値 < joints の数 | 検査しない（中身） | － |
| MUST-107 | 2345 | Texture Data > Textures | テクスチャの画像の形式 | 検査しない（中身） | － |
| MUST-108 | 2386 | Images > Overview | 画像は bufferView と uri のどちらか一方 | 検証した | `validate::resource::image_ok` |
| MUST-109 | 2388 | Images > Overview | 画像の data URL のメディアタイプと中身 | 検査しない（中身） | － |
| MUST-110 | 2390 | Images > Overview | 画像の bufferView は byteStride / target なし | 検証した | `validate::data::stride_ok`, `target_ok` |
| MUST-111 | 2398 | Images > Overview | mimeType と画像の形式の一致 | 検査しない（中身） | － |
| MUST-112 | 2398 | Images > Overview | bufferView の画像には mimeType が必要 | 検証した | `validate::resource::image_ok` |
| MUST-113 | 2430 | Images > Overview | 色空間の情報を無視する（クライアント） | 対象外（クライアント） | － |
| MUST-114 | 2445 | Images > PNG Support | PNG は image/png | 検査しない（中身） | － |
| MUST-115 | 2483 | Images > JPEG Support | JPEG は image/jpeg | 検査しない（中身） | － |
| MUST-116 | 2485 | Images > JPEG Support | JPEG は JFIF | 検査しない（中身） | － |
| MUST-117 | 2487 | Images > JPEG Support | JPEG の APP0 | 検査しない（中身） | － |
| MUST-118 | 2488 | Images > JPEG Support | JPEG の成分 | 検査しない（中身） | － |
| MUST-119 | 2489 | Images > JPEG Support | JPEG の色モデル | 検査しない（中身） | － |
| MUST-120 | 2503 | Images > JPEG Support | JPEG の SOF | 検査しない（中身） | － |
| MUST-121 | 2510 | Images > JPEG Support | JPEG の DNL | 検査しない（中身） | － |
| MUST-122 | 2517 | Images > JPEG Support | ICC プロファイルを無視する（クライアント） | 対象外（クライアント） | － |
| MUST-123 | 2536 | Samplers > Overview | ラップモードに従う（クライアント） | 対象外（クライアント） | － |
| MUST-124 | 2648 | Materials > Overview | テクスチャを使うマテリアルなら TEXCOORD が必要 | 検証した | `validate::mesh::material_texcoords_ok` |
| MUST-125 | 2696 | Materials > Metallic-Roughness Material | テクスチャの値の符号化 | 検査しない（中身） | － |
| MUST-126 | 2698 | Materials > Metallic-Roughness Material | テクスチャの値の符号化 | 検査しない（中身） | － |
| MUST-127 | 2698 | Materials > Metallic-Roughness Material | テクスチャの値の符号化 | 検査しない（中身） | － |
| MUST-128 | 2723 | Materials > Metallic-Roughness Material | テクスチャの値の符号化 | 検査しない（中身） | － |
| MUST-129 | 2774 | Materials > Emissive Parameter | テクスチャの値の符号化 | 検査しない（中身） | － |
| MUST-130 | 2854 | Additional Textures > Normal Texture | テクスチャの値の符号化 | 検査しない（中身） | － |
| MUST-131 | 2872 | Additional Textures > Occlusion Texture | テクスチャの値の符号化 | 検査しない（中身） | － |
| MUST-132 | 2979 | Cameras > Overview | camera.type が必要 | 検証した | `read::objects::read_camera` |
| MUST-133 | 2981 | Cameras > Overview | perspective なら perspective が必要 | 検証した | `validate::cameras_ok` |
| MUST-134 | 2981 | Cameras > Overview | orthographic なら orthographic が必要 | 検証した | `validate::cameras_ok` |
| MUST-135 | 3063 | Projection Matrices > Infinite Perspective Projection | 投影のパラメーター > 0 | 検査しない（浮動小数点） | － |
| MUST-136 | 3074 | Projection Matrices > Finite Perspective Projection | 投影のパラメーター > 0 | 検査しない（浮動小数点） | － |
| MUST-137 | 3078 | Projection Matrices > Finite Perspective Projection | zfar > znear | 検査しない（浮動小数点） | － |
| MUST-138 | 3085 | Projection Matrices > Orthographic Projection | xmag, ymag ≠ 0 | 検査しない（浮動小数点） | － |
| MUST-139 | 3087 | Projection Matrices > Orthographic Projection | znear ≥ 0 | 検査しない（浮動小数点） | － |
| MUST-140 | 3089 | Projection Matrices > Orthographic Projection | zfar > 0, zfar > znear | 検査しない（浮動小数点） | － |
| MUST-141 | 3130 | Animation Samplers > Input Accessor | アニメーションの入力は SCALAR float32 で min / max あり | 検証した | `validate::animation::animation_samplers_ok` |
| MUST-142 | 3132 | Animation Samplers > Input Accessor | 入力の bufferView は byteStride / target なし | 検証した | `validate::data::stride_ok`, `target_ok` |
| MUST-143 | 3134 | Animation Samplers > Input Accessor | 時刻は 0 以上で昇順 | 検査しない（中身） | － |
| MUST-144 | 3136 | Animation Samplers > Input Accessor | 時刻に無限大・NaN がない | 検査しない（中身） | － |
| MUST-145 | 3151 | Animation Samplers > Interpolation | CUBICSPLINE の入力は 2 要素以上 | 検証した | `validate::animation::animation_samplers_ok` |
| MUST-146 | 3158 | Animation Samplers > Output Accessor | 出力の bufferView は byteStride / target なし | 検証した | `validate::data::stride_ok`, `target_ok` |
| MUST-147 | 3166 | Animation Samplers > Output Accessor | キーフレームに無限大・NaN がない | 検査しない（中身） | － |
| MUST-148 | 3278 | Animation Channels > Channel Target | アニメーションの対象はアニメーション可能なプロパティ | 検証した | `validate::animation::channel_ok` |
| MUST-149 | 3295 | Animation Channels > Channel Sampler | 出力のアクセサーの型 | 検証した | `validate::animation::output_type_ok` |
| MUST-150 | 3314 | Animation Channels > Channel Sampler | 出力の要素数 | 検証した | `validate::animation::output_count_ok` |
| MUST-151 | 3316 | Animation Channels > Channel Sampler | 回転の出力は単位四元数 | 検査しない（中身） | － |
| MUST-152 | 3329 | Animations > Applying Animation Data | 1 つのアニメーションの対象は重複なし | 検証した | `validate::animation::target_unique` |
| MUST-153 | 3666 | Specifying Extensions | 使う拡張は extensionsUsed に列挙 | 検証した | `validate::extensions_ok` |
| MUST-154 | 3666 | Specifying Extensions | extensionsUsed は重複なし | 検証した | `validate::extensions_ok` |
| MUST-155 | 3682 | Specifying Extensions | 読み込みに必要な拡張は extensionsRequired に列挙（拡張の意味による。このローダーは extensionsRequired が空でなければ Unsupported） | 対象外（拡張の意味） | － |
| MUST-156 | 3682 | Specifying Extensions | extensionsRequired は重複なし | 検証した | `validate::extensions_ok` |
| MUST-157 | 3700 | Specifying Extensions | extensionsRequired ⊆ extensionsUsed | 検証した | `validate::extensions_ok` |
| MUST-158 | 3749 | Binary glTF Layout > GLB Header | GLB の magic | 検証した | `glb::parse_glb` |
| MUST-159 | 3792 | Chunks > Chunk Structure (GLBv2) | chunkLength は 4 の倍数 | 検証した | `glb::scan_chunks` |
| MUST-160 | 3811 | Chunk Types > Structured JSON Content | JSON チャンクは最初に 1 つだけ | 検証した | `glb::scan_chunks` |
| MUST-161 | 3830 | Chunk Types > Binary Buffer | BIN チャンクは 2 番目に 1 つまで | 検証した | `glb::scan_chunks` |
| MUST-162 | 4072 | Material Structure > Complete Model | BRDF の性質（描画） | 対象外（クライアント） | － |
