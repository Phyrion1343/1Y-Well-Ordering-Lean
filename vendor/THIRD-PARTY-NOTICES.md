# Third-party source notices

The directories listed below contain source snapshots from other projects. Their upstream license terms and attribution notices remain applicable. The license at the root of this repository does not replace or extend those terms. This document records the observed license information for the pinned snapshots; it does not assign a new license to third-party work.

## Pinned Lean source dependencies

| Directory | Upstream project | Pinned commit | License information in the snapshot |
| --- | --- | --- | --- |
| `mathlib` | [mathlib](https://github.com/leanprover-community/mathlib4) | [`eba3d887fc52c98627f4b81507c0efc3096e91b9`](https://github.com/leanprover-community/mathlib4/tree/eba3d887fc52c98627f4b81507c0efc3096e91b9) | [Apache-2.0](mathlib/LICENSE) |
| `LeanSearchClient` | [LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient) | [`0498c7c070c143a3bf7379f4d99a2c63bb9d9715`](https://github.com/leanprover-community/LeanSearchClient/tree/0498c7c070c143a3bf7379f4d99a2c63bb9d9715) | [Apache-2.0](LeanSearchClient/LICENSE) |
| `importGraph` | [importGraph](https://github.com/leanprover-community/import-graph) | [`18a90119a5d316358fde6c86e0ca24e59212e32c`](https://github.com/leanprover-community/import-graph/tree/18a90119a5d316358fde6c86e0ca24e59212e32c) | [Apache-2.0](importGraph/LICENSE) |
| `proofwidgets` | [proofwidgets](https://github.com/leanprover-community/ProofWidgets4) | [`b1436dc749e722c9920036b52cdc43b3451d0b69`](https://github.com/leanprover-community/ProofWidgets4/tree/b1436dc749e722c9920036b52cdc43b3451d0b69) | [Apache-2.0](proofwidgets/LICENSE) |
| `Cli` | [Cli](https://github.com/leanprover/lean4-cli) | [`da07ca808b6718cb2aed14dba154e5a08b8f8ecf`](https://github.com/leanprover/lean4-cli/tree/da07ca808b6718cb2aed14dba154e5a08b8f8ecf) | [MIT](Cli/LICENSE) |
| `aesop` | [aesop](https://github.com/leanprover-community/aesop) | [`57d3325be72a842920813bcb40f96a6f7393c185`](https://github.com/leanprover-community/aesop/tree/57d3325be72a842920813bcb40f96a6f7393c185) | [Apache-2.0](aesop/LICENSE) |
| `Qq` | [Qq](https://github.com/leanprover-community/quote4) | [`ee41917ae11d38479fb8fb24745f7ca4bf0a784d`](https://github.com/leanprover-community/quote4/tree/ee41917ae11d38479fb8fb24745f7ca4bf0a784d) | [Apache-2.0](Qq/LICENSE) |
| `batteries` | [batteries](https://github.com/leanprover-community/batteries) | [`2c810760f0a0c4536b397dbe30ca9b2f2f467366`](https://github.com/leanprover-community/batteries/tree/2c810760f0a0c4536b397dbe30ca9b2f2f467366) | [Apache-2.0](batteries/LICENSE) |
| `plausible` | [plausible](https://github.com/leanprover-community/plausible) | [`b1c4a69a7e247ab7df20460212001673d74f08c0`](https://github.com/leanprover-community/plausible/tree/b1c4a69a7e247ab7df20460212001673d74f08c0) | [Apache-2.0](plausible/LICENSE) |
| `bms` | [YesMetaZFC and bms-constructible-bridge](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean) | [`bae7e3d741f24a56d80da9b99c1345562cd10c2d`](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/tree/bae7e3d741f24a56d80da9b99c1345562cd10c2d) | No license file in the pinned snapshot; see the BMS note below |
| `cu` | [lean-constructible-universe](https://github.com/05-02-07/lean-constructible-universe) | [`7f5a7d03d63d9769172f17350bbe8303996e5b53`](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53) | [Apache-2.0](cu/LICENSE) |

The original `LICENSE` files and source copyright/author notices are retained. The Apache-2.0 packages permit redistribution subject to their license conditions, including retention of notices and identification of modifications. Cli's MIT notice credits **Copyright (c) 2021 mhuisi** and must remain with its permission text. These package-level entries do not override separately licensed assets or embedded components.

### BMS / YesMetaZFC license status

The fixed BMS snapshot `bae7e3d741f24a56d80da9b99c1345562cd10c2d` contains no `LICENSE`, `COPYING`, or `NOTICE` file, and no general license grant was found in its README. It credits the [lanxinge/YesMetaZFC](https://github.com/lanxinge/YesMetaZFC) baseline `b36e243` for its logic and set-theory foundation.

This release bundles the snapshot following confirmation by this project's maintainer, who states that they will ask the upstream maintainers to add an Apache license. An upstream license file has **not** yet been supplied with this pinned snapshot. This notice does **not** assert that BMS, YesMetaZFC, or their contributors' work is already covered by this repository's Apache-2.0 license. Any later upstream license addition should be recorded with its actual scope and applicable revision.

Upstream attribution is preserved in [bms/README.md](bms/README.md). The two local BMS proof-performance patches are documented in [the patch directory](../formalization/Concrete/patches/), including their upstream baseline and before/after source hashes; the patched files are not represented as unmodified upstream files.

## ProofWidgets JavaScript assets

The pinned ProofWidgets source includes `widget/js/lake.trace` and 23 generated JavaScript files. Their existing license comments, copyright notices, package metadata, and bundled contents are retained. The Apache-2.0 license of ProofWidgets itself is not a blanket license for every embedded third-party component.

Three components are explicitly identifiable from license comments in the generated JavaScript and their versions in the pinned `widget/package-lock.json`:

| Component | Version | Identifying bundled file(s) | Additional license text |
| --- | --- | --- | --- |
| Three.js | 0.183.1 | `proofwidgets/widget/js/rubiks.js` | [MIT license](licenses/proofwidgets-npm/three-0.183.1/LICENSE) |
| react-reconciler | 0.27.0 | `proofwidgets/widget/js/rubiks.js` | [MIT license](licenses/proofwidgets-npm/react-reconciler-0.27.0/LICENSE) |
| mhchemparser | 4.2.1 | `proofwidgets/widget/js/penroseCanvas.js`, `penroseDisplay.js` | [Apache-2.0 license](licenses/proofwidgets-npm/mhchemparser-4.2.1/LICENSE.txt) |

The corresponding attribution includes the Three.js authors, Facebook, Inc. and its affiliates, and Martin Hensel. Exact wording is preserved in the original JavaScript and the copied license texts.

The [supplemental license directory](licenses/README.md) also retains license/notice texts obtained from a conservative collection of non-development packages in that same locked npm dependency graph. Its [source manifest](licenses/proofwidgets-npm-sources.json) records exact package versions, archive URLs, locked integrity values, verification results, archive member paths, and copied-file SHA-256 hashes. Inclusion in that collection does **not** mean that the package appears in a generated JavaScript bundle. Some npm archives contain no separate license file; the manifest records those cases without fabricating a license text.

This is a source and attribution inventory, **not a complete audit of all transitive npm licenses or generated bundle contents**. No extra npm runtime source code is distributed by this supplemental license collection, and it is not used by the Lean build.
