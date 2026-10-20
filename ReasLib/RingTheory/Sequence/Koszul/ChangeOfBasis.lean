/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import ReasLib.RingTheory.Sequence.Koszul.Family
public import ReasLib.RingTheory.Sequence.Koszul.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Changing a finite family of Koszul generators

An invertible matrix changes a finite family of generators without changing its Koszul complex.
The chain maps are explicit maps induced on exterior powers; only their inverse laws are deferred.

@stack 0625
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Module
open scoped Matrix

namespace KoszulComplex

variable {R : Type u} [CommRing R]

/-- An invertible matrix changes the finite-family linear form by its transpose. -/
@[stacks 0625 "linear form under an invertible change of generators"]
theorem linearForm_matrixTranspose {r : ℕ} (x : Matrix (Fin r) (Fin r) R)
    (f : Fin r → R) :
    koszulLinearForm (x.toLin' f) = (koszulLinearForm f).comp (xᵀ).toLin' := sorry

/-- Precomposing the changed linear form with the inverse transpose recovers the original form. -/
@[stacks 0625 "inverse-transpose compatibility of the changed linear form"]
theorem linearForm_matrixTranspose_comp_inv {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) :
    (koszulLinearForm (x.toLin' f)).comp (⅟ (xᵀ)).toLin' = koszulLinearForm f := sorry

/-- The forward Koszul map attached to an invertible change of generators. -/
@[stacks 0625 "forward Koszul map under a change of generators"]
noncomputable def matrixLinearCombinationHom {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) :
    family f ⟶ family (x.toLin' f) :=
  map (⅟ (xᵀ)).toLin' (linearForm_matrixTranspose_comp_inv x f)

/-- The inverse Koszul map attached to an invertible change of generators. -/
@[stacks 0625 "inverse Koszul map under a change of generators"]
noncomputable def matrixLinearCombinationInv {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) :
    family (x.toLin' f) ⟶ family f :=
  map (xᵀ).toLin' (linearForm_matrixTranspose x f).symm

/-- The forward and inverse change-of-generators maps compose to the identity on the source. -/
@[stacks 0625 "forward-inverse law for the Koszul change of generators"]
theorem matrixLinearCombinationHom_inv_id {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) :
    matrixLinearCombinationHom x f ≫ matrixLinearCombinationInv x f = 𝟙 (family f) := sorry

/-- The inverse and forward change-of-generators maps compose to the identity on the target. -/
@[stacks 0625 "inverse-forward law for the Koszul change of generators"]
theorem matrixLinearCombinationInv_hom_id {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) :
    matrixLinearCombinationInv x f ≫ matrixLinearCombinationHom x f =
      𝟙 (family (x.toLin' f)) := sorry

/-- Lemma 15.28.4: an invertible linear change of a finite family of generators induces an
isomorphism of the corresponding Koszul complexes. -/
@[stacks 0625 "Lemma 15.28.4"]
noncomputable def matrixLinearCombinationIso {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) :
    family f ≅ family (x.toLin' f) :=
  CategoryTheory.Iso.mk (matrixLinearCombinationHom x f) (matrixLinearCombinationInv x f)
    (matrixLinearCombinationHom_inv_id x f) (matrixLinearCombinationInv_hom_id x f)

/-- The degree-`n` component of the forward change-of-generators map is induced by the inverse
transpose. -/
@[stacks 0625 "components of the Koszul change-of-generators isomorphism"]
theorem matrixLinearCombinationIso_hom_f {r : ℕ}
    (x : Matrix (Fin r) (Fin r) R) [Invertible x] (f : Fin r → R) (n : ℕ) :
    (matrixLinearCombinationIso x f).hom.f n = mapComponent (⅟ (xᵀ)).toLin' n := sorry

end KoszulComplex
