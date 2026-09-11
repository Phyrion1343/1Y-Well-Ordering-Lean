# Supplemental ProofWidgets license texts

These are verbatim license, copyright, and notice files copied from exact-version npm package archives referenced by the pinned ProofWidgets `widget/package-lock.json`, at ProofWidgets commit `b1436dc749e722c9920036b52cdc43b3451d0b69`. Package archives were checked against the lockfile's integrity value before any text was copied. The lockfile, archive, and individual text hashes are recorded in [proofwidgets-npm-sources.json](proofwidgets-npm-sources.json).

## Scope

The collection considers **281 non-development package/version entries** from the lockfile, a conservative superset rather than a reconstruction of the generated bundles. It preserves **283 license/notice files (412,805 bytes)**. There were **15 entries without a separate matching license/notice file** in their npm archive; those entries remain in the manifest with their observed package metadata. No license text was invented for them. Fetch/integrity failures: **0**. Some `@types` archives use a package-specific root directory; the manifest records the resolved metadata path and the initial reader diagnostic.

Not every listed package, font, example, or notice pertains to code actually embedded in the ProofWidgets JavaScript. An entry's `declaredLicense` and `packageLicense` are upstream metadata, not an independent legal conclusion. This collection is not a complete bundle-license audit and does not assert that every dependency has adequate or mutually compatible licensing. It supplements, rather than replaces, the original source notices.

Only license/notice texts are copied here, not npm package runtime code or archives. The Lean build does not load these files.

## Three components explicitly identified in generated JavaScript

- **Three.js 0.183.1**: `rubiks.js` contains the Three.js MIT notice. [Package MIT license](proofwidgets-npm/three-0.183.1/LICENSE); [exact npm archive](https://registry.npmjs.org/three/-/three-0.183.1.tgz).
- **react-reconciler 0.27.0**: `rubiks.js` contains its React/Facebook MIT notice. [Package MIT license](proofwidgets-npm/react-reconciler-0.27.0/LICENSE); [exact npm archive](https://registry.npmjs.org/react-reconciler/-/react-reconciler-0.27.0.tgz).
- **mhchemparser 4.2.1**: `penroseCanvas.js` and `penroseDisplay.js` contain Martin Hensel's Apache-2.0 notice. [Package license](proofwidgets-npm/mhchemparser-4.2.1/LICENSE.txt); [exact npm archive](https://registry.npmjs.org/mhchemparser/-/mhchemparser-4.2.1.tgz).

See [THIRD-PARTY-NOTICES.md](../THIRD-PARTY-NOTICES.md) for the Lean dependencies and the unresolved upstream license-file status of the pinned BMS/YesMetaZFC snapshot.
