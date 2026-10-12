/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import ReasLib.Algebra.Category.ModuleCat.SymmetricPower
public import ReasLib.LinearAlgebra.TensorPower.Symmetric.Exact

/-!
# Left tensor maps for symmetric powers in `ModuleCat`

This file bundles the canonical map `M ⊗ Sym^n(N) ⟶ Sym^(n + 1)(N)` and its compatibility with
the functorial symmetric-power map.  It is the categorical bridge from the linear-algebra owner
to presheaves and sheaves of modules.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace ModuleCat.symmetricPower

variable {R : Type u} [CommRing R]

/-- The canonical morphism `M ⊗ Sym^n(N) ⟶ Sym^(n + 1)(N)` induced by `f : M ⟶ N`. -/
noncomputable def leftTensorMap {M N : ModuleCat R} (f : M ⟶ N) (n : ℕ) :
    tensorObj M (N.symmetricPower n) ⟶ N.symmetricPower (n + 1) :=
  ModuleCat.ofHom (SymmetricPower.leftTensorMap n f.hom)

/-- The bundled left-tensor morphism sends a pure tensor of pure symmetric tensors to the
corresponding degree-`n + 1` generator. -/
@[simp]
theorem leftTensorMap_tmul_mk {M N : ModuleCat R} (f : M ⟶ N) (n : ℕ)
    (x : M) (m : SymmetricPower.UFin n → N) :
    leftTensorMap f n (x ⊗ₜ mk m) =
      mk (SymmetricPower.cons (f x) m) := sorry

/-- The symmetric-power map induced by `g` annihilates the left-tensor map induced by `f` when
the underlying categorical composite vanishes. -/
theorem map_comp_leftTensorMap_eq_zero {M N P : ModuleCat R}
    (n : ℕ) {f : M ⟶ N} {g : N ⟶ P} (hfg : f ≫ g = 0) :
    leftTensorMap f n ≫ map g (n + 1) = 0 := sorry

end ModuleCat.symmetricPower
