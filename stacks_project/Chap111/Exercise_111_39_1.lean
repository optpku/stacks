/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Exercise_111_39_1_FieldPoint
import Mathlib.Tactic.CrossRefAttribute

/-!
# Field-valued morphisms into standard projective space

The identification of the slice Hom set `Mor_{Spec R}(Spec k, P^n_R)` with the
projectivization `(k^{n+1} \ {0}) / kˣ`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry LinearAlgebra.Projectivization

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Exercise 111.39.1: for a ring `R`, a ring map `φ : R →+* k` to a field, and
`n : ℕ`, the slice Hom `Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ schemeOver R n`
is identified with the projectivization `ℙ k (Fin (n + 1) → k)`, i.e.
`(k^{n+1} \ {0}) / kˣ` acting by scalar multiplication. The morphism
`Spec k ⟶ P^n_k` attached to a class is `fieldPoint`. -/
@[stacks 02A7]
theorem homMk_bijective {R k : Type u} [CommRing R] [Field k] (φ : R →+* k) (n : ℕ) :
    Function.Bijective (homMk φ n) :=
  sorry

end AlgebraicGeometry.ProjectiveSpace
