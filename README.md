# 0-Y / BMS and 1-Y: Expansion, Well-Ordering, and Lean Formalization

**English** | [简体中文](README.zh-CN.md)

This project contains the correspondence between 0-Y and BM4 (the Bashicu Matrix System), well-ordering proofs, and proofs of well-foundedness for the actual 1-Y expansion and well-ordering of its standard generated set. The Lean toolchain is pinned to 4.33.1. The expansion algorithm is defined independently; the HTML expander is provided for visualization and experimentation.

## Proven results for 1-Y

- Every finite sequence of positive integers beginning with 1 reaches the empty sequence under the actual 1-Y expansion, for arbitrary choices of finite copy counts at each step.
- The set of sequences generated from the standard seeds `(1,m)`, `m≥2`, is well-ordered lexicographically. The descendant set of any fixed starting sequence is also well-ordered lexicographically.
- Extraction preserves ancestor relations. The formalization includes contour lifting, reference-edge filling, and complete numerical reconstruction.

**The well-foundedness of the actual 1-Y expansion and the well-ordering of its standard generated set have been formally proved in Lean 4's type theory and verified by the kernel.** The repository also includes a ZFC argument in ordinary mathematical form. The full formal translation of that argument into a first-order ZFC derivation, together with its machine verification, has not yet been completed.

The four final Lean theorems with no explicit parameters are in [ActualWellOrdering.lean](formalization/Concrete/OneYTruth/ActualWellOrdering.lean). The [actual expansion proof](research/1y-well-ordering-proof.md) explains the formalization's structure, and the [ZFC mathematical argument](research/1y-zfc-well-ordering-proof.md) gives the set-theoretic proof.

On 2026-09-12, the combined 0-Y and 1-Y build using the bundled dependency sources completed successfully with 2,015 build tasks. All 14 axiom audits for 0-Y and all 153 for 1-Y passed, using only subsets of `propext`, `Classical.choice`, and `Quot.sound`. See the [validation record](formalization/VALIDATION.md) and [1-Y audit output](formalization/Concrete/OneYTruth-audit-output.txt). This build started in a directory without compiled proof artifacts and was completed through resumed builds. The validation record documents the process and the separate ZIP checks.

The [offline 1-Y expander](1-Y展开器.html) can be opened directly in a browser. The [algorithm and interface documentation](y1/README.md) describes the rules, computation budgets, and testing methods.

## Proven results for 0-Y / BMS

- Encoding and then decoding recovers every valid 0-Y expression.
- A BMS matrix is invertible if and only if it satisfies depth regularity and blocking condition S. Matrices differing only by common trailing zero rows are treated as the same representation.
- All valid 0-Y expressions are order-isomorphic to all invertible BMS matrices, including nonstandard expressions. The encoding also preserves and reflects expansion paths.
- The standard generated set and the expansion-descendant set of any fixed valid starting expression are well-ordered lexicographically.
- From any valid starting expression, expansion reaches the empty expression for arbitrary choices of natural-number indices at each step.
- The full-bad-part convention and the Wiki's finite-endpoint convention have the same reachability closure. Both have the well-ordering and termination properties above.

**The lexicographic order on all valid expressions is not well-founded.** For example, `(1,2) > (1,1,2) > (1,1,1,2) > …`. This counterexample has also been formalized. The well-ordering results apply to the standard generated set or the descendant set of a fixed starting expression.

## Reading guide for 0-Y / BMS

- [Complete mathematical proof](0Y-BMS-equivalence-proof.md): definitions, necessary and sufficient conditions for invertibility, and the ordinary mathematical argument.
- [Formalization guide](formalization/README.md): the Lean declarations corresponding to each result.
- [Final concrete-model theorems](formalization/Concrete/ZeroYConcrete.lean): 13 final theorems using an already constructed model, without requiring the caller to supply an additional descent-bound system.
- [Validation record](formalization/VALIDATION.md): build results, axiom audits, and dependency information.
- [Audit of the upstream interface and extension to nonstandard expressions](research/formalization-bms-interface-audit.md).

On 2026-09-10, the core build completed successfully with 66 tasks, and the full build including the concrete model completed with 1,576 tasks. A total of 57 axiom-dependency audits of key declarations passed, depending only on subsets of `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or custom axioms. These 57 declarations include the concrete model and auxiliary definitions; they are not 57 independent mathematical theorems.

## Building without cloning additional dependency repositories

The repository's `vendor/` directory contains the **11 dependency source repositories** needed for the full build, including the BMS well-ordering formalization, the constructible-universe library, mathlib, and its transitive dependencies. These are ordinary files, not Git submodules, so a copy obtained through **Download ZIP** can also be built. Source versions remain pinned by the [dependency lock file](formalization/Concrete/dependencies-lock.json), and per-file SHA256 hashes are listed in the [source manifest](vendor/source-manifest.json).

You still need the **Lean 4.33.1** compiler. If that version is already available through Lean / elan, use the build commands below directly. Windows users can alternatively run the official portable-toolchain installation script from the repository root first. This installation step requires network access, `curl.exe`, and `tar.exe`:

```powershell
./formalization/prepare-toolchain.ps1
```

From a PowerShell terminal at the repository root, run:

```powershell
./formalization/Concrete/build.ps1
```

This command first verifies the bundled sources locally, then builds the concrete 0-Y and 1-Y proofs, and finally runs their respective 14 and 153 axiom-allowlist audits. **Dependency verification and source compilation require neither network access nor a `.git` directory in any dependency.** To verify only 1-Y:

```powershell
./formalization/Concrete/build.ps1 -Target OneYTruth
```

The script can use the portable Lean installation in the repository, Lean on `PATH`, or an explicitly supplied path via `-LeanBin "path/to/Lean 4.33.1/bin"`. It runs with one thread by default. The first build from source requires substantial time and memory; subsequent builds reuse local artifacts.

To check the dependency sources only, build the core library, or run the 43 core 0-Y axiom audits:

```powershell
./formalization/prepare-dependencies.ps1 -CheckOnly
./formalization/build.ps1
# From the formalization directory, using lake from Lean 4.33.1:
lake --keep-toolchain --no-cache env lean Audit.lean
```

Without PowerShell, after installing Lean 4.33.1, run the following directly from `formalization/Concrete`:

```sh
lake --keep-toolchain --no-cache build ZeroYConcrete OneYTruth
lake --keep-toolchain env lean Audit.lean
lake --keep-toolchain env lean OneYTruthAudit.lean
```

These commands print the axiom dependencies. The PowerShell build script additionally checks declaration names, counts, and the axiom allowlist automatically. The full build has currently been verified on Windows; full builds on other systems have not yet been verified.

In VS Code, open the `formalization/Concrete` folder, then open `OneYTruth/ActualWellOrdering.lean` or `ZeroYConcrete.lean`. Windows users with the portable runtime and elan can register the toolchain from the repository root:

```powershell
elan toolchain link leanprover/lean4:v4.33.1 ./.tools/lean-4.33.1-windows
```

Dependencies are already pinned; there is no need to run `lake update`. See [VALIDATION.md](formalization/VALIDATION.md) for the build and verification record. Third-party sources, licenses, and local build-configuration changes are documented in [vendor/README.md](vendor/README.md).

## Upstream work

The well-ordering model reuses the constructible-universe bridge from [EgoFakeFantasy/BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean), pinned to `bae7e3d741f24a56d80da9b99c1345562cd10c2d`, with two proof-performance patches. Other dependencies of the concrete model include constructible-universe and mathlib. Their sources are bundled in `vendor/`; exact origins and commits are recorded in the lock file.

For mathematical background, see Rachel Hunter's [Well-Orderedness of the Bashicu Matrix System](https://arxiv.org/abs/2307.04606) and the [Googology Wiki definition of 0-Y](https://wiki.googology.top/index.php/0-Y). External reference HTML files, compiled dependency caches, and local diagnostic materials are not included in the release.

The project itself retains the existing [Apache-2.0 license](LICENSE). Third-party files in `vendor/` are provided under their respective licenses and source notices; see the [third-party notices](vendor/THIRD-PARTY-NOTICES.md).
