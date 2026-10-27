/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Retract
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

open CategoryTheory Limits ObjectProperty Opposite Pretriangulated ZeroObject

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
    IsClosedUnderIsomorphisms (property RΓ restrict comparison) where
  of_iso e h _ _ f := (NatTrans.isIso_app_iff_of_iso (comparison f) e).mp (h f)

/-- A comparison-isomorphism locus is stable under retracts. -/
@[stacks 0GYW "comparison locus is stable under retracts",
  stacks 0GZA "comparison locus is stable under retracts"]
instance isStableUnderRetracts :
    IsStableUnderRetracts (property RΓ restrict comparison) where
  of_retract h hY U _ f :=
    MorphismProperty.of_retract (P := MorphismProperty.isomorphisms (E U))
      ((comparison f).retractArrowApp h) (hY f)

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
    ObjectProperty.IsTriangulated (property RΓ restrict comparison) where
  exists_zero := ⟨0, isZero_zero D, by
    intro U V f
    exact ((RΓ V ⋙ restrict f).map_isZero (isZero_zero D)).isIso
      ((RΓ U).map_isZero (isZero_zero D)) _⟩
  isStableUnderShiftBy n := ⟨by
    intro X hX U V f
    haveI : IsIso ((comparison f).app X) := hX f
    change IsIso ((comparison f).app (X⟦n⟧))
    rw [NatTrans.app_shift (comparison f) n]
    refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ ?_)
    · exact (((RΓ V ⋙ restrict f).commShiftIso n).app X).isIso_hom
    · exact (shiftFunctor (E U) n).map_isIso ((comparison f).app X)
    · exact (((RΓ U).commShiftIso n).app X).isIso_inv⟩
  ext₂' T hT h₁ h₃ := by
    refine ⟨T.obj₂, ?_, ⟨Iso.refl _⟩⟩
    intro U V f
    let φ : (RΓ V ⋙ restrict f).mapTriangle.obj T ⟶ (RΓ U).mapTriangle.obj T :=
      { hom₁ := (comparison f).app T.obj₁
        hom₂ := (comparison f).app T.obj₂
        hom₃ := (comparison f).app T.obj₃
        comm₁ := (comparison f).naturality T.mor₁
        comm₂ := (comparison f).naturality T.mor₂
        comm₃ := by
          change ((RΓ V ⋙ restrict f).map T.mor₃ ≫
              ((RΓ V ⋙ restrict f).commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
                ((comparison f).app T.obj₁)⟦(1 : ℤ)⟧' =
            (comparison f).app T.obj₃ ≫ ((RΓ U).map T.mor₃ ≫
              ((RΓ U).commShiftIso (1 : ℤ)).hom.app T.obj₁)
          calc
            _ = (RΓ V ⋙ restrict f).map T.mor₃ ≫
                (((RΓ V ⋙ restrict f).commShiftIso (1 : ℤ)).hom.app T.obj₁ ≫
                  ((comparison f).app T.obj₁)⟦(1 : ℤ)⟧') := Category.assoc _ _ _
            _ = (RΓ V ⋙ restrict f).map T.mor₃ ≫
                ((comparison f).app (T.obj₁⟦(1 : ℤ)⟧) ≫
                  ((RΓ U).commShiftIso (1 : ℤ)).hom.app T.obj₁) :=
              congrArg (fun k ↦ (RΓ V ⋙ restrict f).map T.mor₃ ≫ k)
                (NatTrans.shift_app_comm (comparison f) (1 : ℤ) T.obj₁)
            _ = ((RΓ V ⋙ restrict f).map T.mor₃ ≫
                (comparison f).app (T.obj₁⟦(1 : ℤ)⟧)) ≫
                  ((RΓ U).commShiftIso (1 : ℤ)).hom.app T.obj₁ :=
              (Category.assoc _ _ _).symm
            _ = ((comparison f).app T.obj₃ ≫ (RΓ U).map T.mor₃) ≫
                ((RΓ U).commShiftIso (1 : ℤ)).hom.app T.obj₁ :=
              congrArg (fun k ↦ k ≫ ((RΓ U).commShiftIso (1 : ℤ)).hom.app T.obj₁)
                ((comparison f).naturality T.mor₃)
            _ = _ := Category.assoc _ _ _ }
    exact isIso₂_of_isIso₁₃ φ ((RΓ V ⋙ restrict f).map_distinguished T hT)
      ((RΓ U).map_distinguished T hT) (h₁ f) (h₃ f)

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
    IsClosedUnderColimitsOfShape (property RΓ restrict comparison) J where
  colimitsOfShape_le := by
    rintro X ⟨h⟩ U V f
    haveI : ∀ j, IsIso ((Functor.whiskerLeft h.diag (comparison f)).app j) :=
      fun j ↦ h.prop_diag_obj j f
    haveI : IsIso (Functor.whiskerLeft h.diag (comparison f)) := NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit h.diag (comparison f) _ h.isColimit

/-- If all section and restriction functors preserve `ι`-indexed coproducts, then so does the
comparison-isomorphism locus. -/
@[stacks 0GYW "direct sums in a comparison locus",
  stacks 0GZA "direct sums in a comparison locus"]
theorem isClosedUnderDirectSums (ι : Type w)
    [∀ U : C, PreservesColimitsOfShape (Discrete ι) (RΓ U)]
    [∀ {U V : C} (f : U ⟶ V), PreservesColimitsOfShape (Discrete ι) (restrict f)] :
    IsClosedUnderColimitsOfShape (property RΓ restrict comparison) (Discrete ι) :=
  isClosedUnderColimitsOfShape RΓ restrict comparison (Discrete ι)

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
    IsClosedUnderIsomorphisms (isQuasiCoherent 𝒪 RΓ restrict comparison) :=
  QuasiCoherent.isClosedUnderIsomorphisms RΓ restrict comparison

/-- Lemma 21.43.2 (2) and Lemma 24.33.2 (2): the comparison-defined subcategory `QC` is stable
under retracts. -/
@[stacks 0GYW, stacks 0GZA]
instance qc_isStableUnderRetracts :
    IsStableUnderRetracts (isQuasiCoherent 𝒪 RΓ restrict comparison) :=
  QuasiCoherent.isStableUnderRetracts RΓ restrict comparison

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
    ObjectProperty.IsTriangulated (isQuasiCoherent 𝒪 RΓ restrict comparison) :=
  QuasiCoherent.isTriangulated RΓ restrict comparison

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
    IsClosedUnderColimitsOfShape (isQuasiCoherent 𝒪 RΓ restrict comparison) J :=
  QuasiCoherent.isClosedUnderColimitsOfShape RΓ restrict comparison J

/-- Lemma 21.43.2 (4) and Lemma 24.33.2 (4): if the section and restriction functors preserve
`ι`-indexed coproducts, then `QC` is closed under those coproducts. -/
@[stacks 0GYW, stacks 0GZA]
theorem qc_isClosedUnderDirectSums (ι : Type w)
    [∀ U : C, PreservesColimitsOfShape (Discrete ι) (RΓ U)]
    [∀ {U V : C} (f : U ⟶ V), PreservesColimitsOfShape (Discrete ι) (restrict f)] :
    IsClosedUnderColimitsOfShape
      (isQuasiCoherent 𝒪 RΓ restrict comparison) (Discrete ι) :=
  QuasiCoherent.isClosedUnderDirectSums RΓ restrict comparison ι

end Colimits

end CategoryTheory.ModulesOnCategory
