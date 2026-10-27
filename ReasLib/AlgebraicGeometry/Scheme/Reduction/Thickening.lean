/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

/-! # Reduction of thickenings -/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The kernel of a thickening vanishes on the reduction of its target. -/
theorem ker_le_ker_reductionι_of_isThickening {A B : Scheme.{u}} (f : A ⟶ B)
    [IsThickening f] : f.ker ≤ (Scheme.reductionι B).ker := sorry

/-- The inverse map on reductions of a thickening, obtained by closed-subscheme lifts. -/
def reductionInvOfThickening {A B : Scheme.{u}} (f : A ⟶ B) [IsThickening f] :
    Scheme.reduction B ⟶ Scheme.reduction A :=
  reductionLift (IsClosedImmersion.lift f (Scheme.reductionι B)
    (ker_le_ker_reductionι_of_isThickening f))

/-- The reduced map of a thickening followed by its explicit inverse is the identity. -/
theorem reductionMap_comp_reductionInvOfThickening {A B : Scheme.{u}} (f : A ⟶ B)
    [IsThickening f] :
    Scheme.reductionMap f ≫ reductionInvOfThickening f = 𝟙 (Scheme.reduction A) := sorry

/-- The explicit inverse followed by the reduced map of a thickening is the identity. -/
theorem reductionInvOfThickening_comp_reductionMap {A B : Scheme.{u}} (f : A ⟶ B)
    [IsThickening f] :
    reductionInvOfThickening f ≫ Scheme.reductionMap f = 𝟙 (Scheme.reduction B) := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Over

/-- A thickening of schemes over a base induces an isomorphism of their reductions. -/
def reductionIsoOfThickening {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B)
    [IsThickening f.left] : reduction A ≅ reduction B where
  hom := reductionMap f
  inv := Over.homMk (Scheme.Hom.reductionInvOfThickening f.left) (by
    change Scheme.Hom.reductionInvOfThickening f.left ≫
      (Scheme.reductionι A.left ≫ A.hom) = Scheme.reductionι B.left ≫ B.hom
    rw [← f.w, ← Category.assoc (Scheme.reductionι A.left) f.left B.hom,
      ← Scheme.reductionMap_reductionι f.left]
    simp only [← Category.assoc,
      Scheme.Hom.reductionInvOfThickening_comp_reductionMap, Category.id_comp])
  hom_inv_id := by
    apply Over.OverMorphism.ext
    exact Scheme.Hom.reductionMap_comp_reductionInvOfThickening f.left
  inv_hom_id := by
    apply Over.OverMorphism.ext
    exact Scheme.Hom.reductionInvOfThickening_comp_reductionMap f.left

end AlgebraicGeometry.Over
