/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.Relative
public import ReasLib.Algebra.Homology.CochainComplex.TensorProduct.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# K-flat complexes over a commutative ring

The ambient monoidal structure on `ModuleCat R` only covers modules in the universe of `R`.
This file specializes relative K-flatness to the universe-polymorphic ground tensor bifunctor.
@stack 06XZ
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- A module-valued cochain complex is K-flat over `R` if tensoring it with an acyclic complex
over `R` gives an acyclic total complex.  Its carrier universe may differ from that of `R`. -/
@[stacks 06XZ "module-complex form"]
def IsKFlatOver (K : CochainComplex (ModuleCat.{v} R) ℤ) : Prop :=
  K.IsKFlatFor (ModuleCat.TensorProduct.functor.{u, v, v} R)

/-- Tensoring an acyclic complex over `R` with a K-flat complex over `R` gives an acyclic total
complex. -/
lemma IsKFlatOver.acyclic_tensor {K : CochainComplex (ModuleCat.{v} R) ℤ}
    (hK : K.IsKFlatOver) {M : CochainComplex (ModuleCat.{v} R) ℤ}
    [TensorProduct.HasTotal M K] (hM : M.Acyclic) :
    (TensorProduct.obj M K).Acyclic := sorry

/-- K-flatness over `R` is exactly preservation of acyclicity by the total ground tensor
product. -/
theorem isKFlatOver_iff (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    K.IsKFlatOver ↔
      ∀ ⦃M : CochainComplex (ModuleCat.{v} R) ℤ⦄
        [TensorProduct.HasTotal M K],
          M.Acyclic → (TensorProduct.obj M K).Acyclic := sorry

end CochainComplex
