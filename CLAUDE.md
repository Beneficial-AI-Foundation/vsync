# vsync — formally verified rsync core in Lean 4

## Workflow
- Source of truth is this directory; `./vd.sh push|build|pull|all` rsyncs it to `VD:~/vsync`,
  runs `lake build VSync +Main` there (Lean 4.36.0, no Mathlib — VD has 3 GB RAM), and pulls the
  generated C into `./c/`. VD cannot compile C (glibc too old for Lean's clang).
- `./build-local.sh` compiles `./c/` with the local leanc into `build-local/vsync`.

## Specs, not tests
- There are no runtime unit tests. `VSync/Spec.lean` is the test suite: every behaviour is a
  theorem checked by `lake build`.
- Any new or changed behaviour gets a spec in `VSync/Spec.lean` (in the matching section, with a
  docstring saying what it guarantees), and a `#guard_msgs` + `#print axioms` entry in the audit
  section at the bottom. Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.
- State specs for all inputs. Concrete examples only if kernel-checkable (`rfl`/`decide`);
  never `native_decide`.
- Supporting lemmas go in `VSync/Proofs.lean`; `Spec.lean` stays a readable list of guarantees.
- When a spec needs an assumption (e.g. `NoCollision`), make it satisfiable — never assume a
  property that is false for the real implementation (e.g. "the hash is injective").
- Not covered by specs: the IO shell in `Main.lean` (file reads/writes, atomic rename).
