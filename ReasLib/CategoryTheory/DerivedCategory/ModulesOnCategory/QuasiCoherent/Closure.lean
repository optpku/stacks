/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent

/-!
# Closure properties of comparison-defined quasi-coherent objects

The full subcategory cut out by derived restriction comparisons is invariant under isomorphisms
and retracts.  Exact comparison data makes it triangulated, and colimit-preserving comparison data
makes it closed under the corresponding colimits.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits ObjectProperty Opposite Pretriangulated

universe w uJ vJ uC vC uD vD uE vE

namespace CategoryTheory.ModulesOnCategory

namespace QuasiCoherent

section Basic

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : C → Type uE} [∀ U, Category.{vE} (E U)]
variable (RΓ : ∀ U : C, D ⥤ E U)
variable (restrict : ∀ {U V : C}, (U ⟶ V) → E V ⥤ E U)
variable
  (comparison : ∀ {U V : C} (f : U ⟶ V),
    RΓ V ⋙ restrict f ⟶ RΓ U)

/-- A comparison-isomorphism locus is invariant under isomorphisms of ambient objects. -/
@[stacks 0GYW "comparison locus is strictly full", stacks 0GZA "comparison locus is strictly full"]
instance isClosedUnderIsomorphisms :
    IsClosedUnderIsomorphisms (property RΓ restrict comparison) := sorry

/-- A comparison-isomorphism locus is stable under retracts. -/
@[stacks 0GYW "comparison locus is stable under retracts",
  stacks 0GZA "comparison locus is stable under retracts"]
instance isStableUnderRetracts :
    IsStableUnderRetracts (property RΓ restrict comparison) := sorry

end Basic

section Triangulated

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {E : C → Type uE} [∀ U, Category.{vE} (E U)]
variable [∀ U, HasZeroObject (E U)] [∀ U, HasShift (E U) ℤ]
variable [∀ U, Preadditive (E U)]
variable [∀ U, ∀ n : ℤ, (shiftFunctor (E U) n).Additive]
variable [∀ U, Pretriangulated (E U)]
variable (RΓ : ∀ U : C, D ⥤ E U)
variable (restrict : ∀ {U V : C}, (U ⟶ V) → E V ⥤ E U)
variable
  (comparison : ∀ {U V : C} (f : U ⟶ V),
    RΓ V ⋙ restrict f ⟶ RΓ U)

/-- Exact section and restriction functors with shift-compatible comparisons make the
comparison-isomorphism locus triangulated. -/
@[stacks 0GYW "triangulated comparison locus", stacks 0GZA "triangulated comparison locus"]
instance isTriangulated
    [∀ U : C, (RΓ U).CommShift ℤ] [∀ U : C, (RΓ U).IsTriangulated]
    [∀ {U V : C} (f : U ⟶ V), (restrict f).CommShift ℤ]
    [∀ {U V : C} (f : U ⟶ V), (restrict f).IsTriangulated]
    [∀ {U V : C} (f : U ⟶ V), NatTrans.CommShift (comparison f) ℤ] :
    ObjectProperty.IsTriangulated (property RΓ restrict comparison) := sorry

end Triangulated

section Colimits

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : C → Type uE} [∀ U, Category.{vE} (E U)]
variable (RΓ : ∀ U : C, D ⥤ E U)
variable (restrict : ∀ {U V : C}, (U ⟶ V) → E V ⥤ E U)
variable
  (comparison : ∀ {U V : C} (f : U ⟶ V),
    RΓ V ⋙ restrict f ⟶ RΓ U)

/-- A comparison-isomorphism locus is closed under every colimit shape preserved by all section
and restriction functors. -/
@[stacks 0GYW "colimits in a comparison locus", stacks 0GZA "colimits in a comparison locus"]
instance isClosedUnderColimitsOfShape (J : Type uJ) [Category.{vJ} J]
    [∀ U : C, PreservesColimitsOfShape J (RΓ U)]
    [∀ {U V : C} (f : U ⟶ V), PreservesColimitsOfShape J (restrict f)] :
    IsClosedUnderColimitsOfShape (property RΓ restrict comparison) J := sorry

/-- If all section and restriction functors preserve `ι`-indexed coproducts, then so does the
comparison-isomorphism locus. -/
@[stacks 0GYW "direct sums in a comparison locus",
  stacks 0GZA "direct sums in a comparison locus"]
theorem isClosedUnderDirectSums (ι : Type w)
    [∀ U : C, PreservesColimitsOfShape (Discrete ι) (RΓ U)]
    [∀ {U V : C} (f : U ⟶ V), PreservesColimitsOfShape (Discrete ι) (restrict f)] :
    IsClosedUnderColimitsOfShape (property RΓ restrict comparison) (Discrete ι) := sorry

end Colimits

end QuasiCoherent

section Basic

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
variable (RΓ : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (restrict : ∀ {U V : C}, (U ⟶ V) →
    DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
      DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison : ∀ {U V : C} (f : U ⟶ V),
    RΓ V ⋙ restrict f ⟶ RΓ U)

/-- Lemma 21.43.2 (1) and Lemma 24.33.2 (1): the comparison-defined subcategory `QC` is
strictly full. -/
@[stacks 0GYW, stacks 0GZA]
instance qc_isClosedUnderIsomorphisms :
    IsClosedUnderIsomorphisms (isQuasiCoherent 𝒪 RΓ restrict comparison) := sorry

/-- Lemma 21.43.2 (2) and Lemma 24.33.2 (2): the comparison-defined subcategory `QC` is stable
under retracts. -/
@[stacks 0GYW, stacks 0GZA]
instance qc_isStableUnderRetracts :
    IsStableUnderRetracts (isQuasiCoherent 𝒪 RΓ restrict comparison) := sorry

end Basic

section Triangulated

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
variable (RΓ : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (restrict : ∀ {U V : C}, (U ⟶ V) →
    DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
      DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison : ∀ {U V : C} (f : U ⟶ V),
    RΓ V ⋙ restrict f ⟶ RΓ U)

/-- Lemma 21.43.2 (3) and Lemma 24.33.2 (3): if the section and restriction functors are exact
and the comparisons commute with shifts, then `QC` is triangulated. -/
@[stacks 0GYW, stacks 0GZA]
instance qc_isTriangulated
    [∀ U : C, (RΓ U).CommShift ℤ] [∀ U : C, (RΓ U).IsTriangulated]
    [∀ {U V : C} (f : U ⟶ V), (restrict f).CommShift ℤ]
    [∀ {U V : C} (f : U ⟶ V), (restrict f).IsTriangulated]
    [∀ {U V : C} (f : U ⟶ V), NatTrans.CommShift (comparison f) ℤ] :
    ObjectProperty.IsTriangulated (isQuasiCoherent 𝒪 RΓ restrict comparison) := sorry

end Triangulated

section Colimits

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
variable (RΓ : ∀ U : C, D ⥤ DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (restrict : ∀ {U V : C}, (U ⟶ V) →
    DerivedCategory (ModuleCat (𝒪.obj (op V))) ⥤
      DerivedCategory (ModuleCat (𝒪.obj (op U))))
variable
  (comparison : ∀ {U V : C} (f : U ⟶ V),
    RΓ V ⋙ restrict f ⟶ RΓ U)

/-- Comparison-defined quasi-coherence is closed under every colimit shape preserved by all
section and restriction functors. -/
@[stacks 0GYW, stacks 0GZA]
instance qc_isClosedUnderColimitsOfShape (J : Type uJ) [Category.{vJ} J]
    [∀ U : C, PreservesColimitsOfShape J (RΓ U)]
    [∀ {U V : C} (f : U ⟶ V), PreservesColimitsOfShape J (restrict f)] :
    IsClosedUnderColimitsOfShape (isQuasiCoherent 𝒪 RΓ restrict comparison) J := sorry

/-- Lemma 21.43.2 (4) and Lemma 24.33.2 (4): if the section and restriction functors preserve
`ι`-indexed coproducts, then `QC` is closed under those coproducts. -/
@[stacks 0GYW, stacks 0GZA]
theorem qc_isClosedUnderDirectSums (ι : Type w)
    [∀ U : C, PreservesColimitsOfShape (Discrete ι) (RΓ U)]
    [∀ {U V : C} (f : U ⟶ V), PreservesColimitsOfShape (Discrete ι) (restrict f)] :
    IsClosedUnderColimitsOfShape
      (isQuasiCoherent 𝒪 RΓ restrict comparison) (Discrete ι) := sorry

end Colimits

end CategoryTheory.ModulesOnCategory
