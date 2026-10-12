/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Graded.LocallyFinite

/-!
# Locally finite graded modules

A ℤ-indexed family of `A`-submodules is locally finite when every piece is a finite `A`-module.
This is independent of the topological predicate `LocallyFinite`, and does not require a
`DirectSum.Decomposition` instance on the family.
-/

@[expose] public section

universe u v

variable {A : Type u} {M : Type v} [CommRing A] [AddCommGroup M] [Module A M]

#check (GradedModule.LocallyFinite : (ℤ → Submodule A M) → Prop)
