/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.RestrictScalars
public import ReasLib.LinearAlgebra.ExteriorPower.Exact

/-!
# Left tensor maps for exterior powers in `ModuleCat`

This file bundles the canonical map `M ⊗ Λ^n(N) ⟶ Λ^(n + 1)(N)` and its compatibility with
functorial exterior-power maps.  It is the categorical bridge from linear algebra to presheaves
and sheaves of modules.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped TensorProduct

noncomputable section

universe u

namespace ModuleCat.exteriorPower

variable {R : Type u} [CommRing R]

/-- The canonical morphism `M ⊗ Λ^n(N) ⟶ Λ^(n + 1)(N)` induced by `f : M ⟶ N`. -/
noncomputable def leftTensorMap {M N : ModuleCat R} (f : M ⟶ N) (n : ℕ) :
    tensorObj M (N.exteriorPower n) ⟶ N.exteriorPower (n + 1) :=
  ModuleCat.ofHom (_root_.exteriorPower.leftTensorMap n f.hom)

/-- The bundled left-tensor morphism sends a pure tensor of an exterior generator to the
generator obtained by prepending its mapped first factor. -/
@[simp]
theorem leftTensorMap_tmul_mk {M N : ModuleCat R} (f : M ⟶ N) (n : ℕ)
    (x : M) (m : Fin n → N) :
    leftTensorMap f n (x ⊗ₜ mk m) = mk (Fin.cons (f x) m) := sorry

/-- The exterior-power map induced by `g` annihilates the left-tensor map induced by `f` when
the underlying categorical composite vanishes. -/
theorem leftTensorMap_comp_eq_zero {M N P : ModuleCat R}
    (n : ℕ) {f : M ⟶ N} {g : N ⟶ P} (hfg : f ≫ g = 0) :
    leftTensorMap f n ≫ map g (n + 1) = 0 := sorry

end ModuleCat.exteriorPower
