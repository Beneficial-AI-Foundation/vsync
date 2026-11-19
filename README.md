# vsync

A formally verified core of the rsync delta algorithm, written in Lean 4 and compiled to C.

- `VSync/Checksum.lean` — rolling weak checksum, with a proof that the O(1) roll equals recomputation.
- `VSync/Delta.lean` — signature / delta / patch.
- `VSync/Proofs.lean` — supporting lemmas.
- `VSync/Spec.lean` — **the test suite**: every guarantee is a theorem checked by `lake build`,
  with an axiom audit that fails the build on `sorry` or non-standard axioms.

Main guarantee (`VSync.Spec.sync_roundtrip`): patching `old` with the delta of `new` reproduces
`new` exactly, provided no window of `new` collides with a different block of `old` under the strong hash.

## Build

```sh
lake build                # check all proofs and build the binary (needs Lean 4.36.0 via elan)
.lake/build/bin/vsync sync <src> <dst> [block-size]
```

Split workflow (proofs + C generation on a remote box, native compile locally):
`./vd.sh all` then `./build-local.sh`.
