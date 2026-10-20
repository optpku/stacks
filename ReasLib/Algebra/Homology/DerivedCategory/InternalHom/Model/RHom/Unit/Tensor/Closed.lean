/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Unit.Tensor
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bundled regular-object tensor-unit comparisons

This leaf specializes the regular-object fixed-left tensor comparisons to the tensor model stored
in an explicit `RHom.ClosedComparison`.  The ambient unit identification remains an input.
@stack 0E1U
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]

/-- The fixed-left regular-object comparison supplied by the bundled tensor model. -/
@[stacks 0E1U "bundled regular fixed-left derived tensor comparison"]
noncomputable abbrev single0LeftDerivedTensorIso
    (P : RHom.ClosedComparison (A := A))
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (K : DerivedCategory (ModuleCat.{u} A))
    [DerivedTensor.Right.Has (C := ModuleCat.{u} A)] :
    DerivedTensor.Right.obj (RHom.Unit.single (A := A)) K ≅ K :=
  RHom.Unit.single0LeftDerivedTensorIso P.tensorModel s K

section Bifunctor

variable [∀ G₁ G₂ : GradedObject ℤ (ModuleCat.{u} A), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ModuleCat.{u} A),
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ModuleCat.{u} A),
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (ModuleCat.{u} A),
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HomotopyCategory.Koszul.TensorDescends (C := ModuleCat.{u} A)]
variable [DerivedTensor.Right.Has (C := ModuleCat.{u} A)]
variable [DerivedTensor.Bifunctor.Has (C := ModuleCat.{u} A)]

/-- The canonical bifunctor unit comparison supplied by the bundled tensor model. -/
@[stacks 0E1U "bundled regular derived bifunctor unit comparison"]
noncomputable abbrev singleBifunctorLeftUnitIso
    (P : RHom.ClosedComparison (A := A))
    (hn : RHom.Unit.BifunctorComparisonIsNatural P.tensorModel)
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A))) :
    RHom.Unit.singlePair (A := A) ⋙
        DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} A) ≅
      𝟭 (DerivedCategory (ModuleCat.{u} A)) :=
  RHom.Unit.bifunctorLeftUnitIso P.tensorModel hn s

/-- The objectwise bundled bifunctor unit comparison. -/
@[stacks 0E1U "bundled regular derived bifunctor unit object comparison"]
noncomputable abbrev singleBifunctorLeftUnitObjIso
    (P : RHom.ClosedComparison (A := A))
    (hn : RHom.Unit.BifunctorComparisonIsNatural P.tensorModel)
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (RHom.Unit.singlePair (A := A) ⋙
      DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} A)).obj K ≅ K :=
  (P.singleBifunctorLeftUnitIso hn s).app K

/-- Naturality of the bundled bifunctor unit comparison. -/
@[reassoc, stacks 0E1U "bundled regular derived bifunctor unit naturality"]
theorem singleBifunctorLeftUnitIso_naturality
    (P : RHom.ClosedComparison (A := A))
    (hn : RHom.Unit.BifunctorComparisonIsNatural P.tensorModel)
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {K L : DerivedCategory (ModuleCat.{u} A)} (f : K ⟶ L) :
    (RHom.Unit.singlePair (A := A) ⋙
        DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} A)).map f ≫
        (P.singleBifunctorLeftUnitIso hn s).hom.app L =
      (P.singleBifunctorLeftUnitIso hn s).hom.app K ≫ f :=
  RHom.Unit.bifunctorLeftUnitIso_naturality P.tensorModel hn s f

/-- Inverse naturality of the bundled bifunctor unit comparison. -/
@[reassoc, stacks 0E1U "inverse bundled regular derived bifunctor unit naturality"]
theorem singleBifunctorLeftUnitIso_inv_naturality
    (P : RHom.ClosedComparison (A := A))
    (hn : RHom.Unit.BifunctorComparisonIsNatural P.tensorModel)
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    {K L : DerivedCategory (ModuleCat.{u} A)} (f : K ⟶ L) :
    f ≫ (P.singleBifunctorLeftUnitIso hn s).inv.app L =
      (P.singleBifunctorLeftUnitIso hn s).inv.app K ≫
        (RHom.Unit.singlePair (A := A) ⋙
          DerivedTensor.Bifunctor.functor (C := ModuleCat.{u} A)).map f :=
  RHom.Unit.bifunctorLeftUnitIso_inv_naturality P.tensorModel hn s f

/-- Agreement between bundled bifunctor and fixed-left comparisons. -/
@[simp, stacks 0E1U "bundled bifunctor and fixed-left unit agreement"]
theorem singleBifunctorLeftUnitIso_agrees_hom
    (P : RHom.ClosedComparison (A := A))
    (hn : RHom.Unit.BifunctorComparisonIsNatural P.tensorModel)
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedTensor.Bifunctor.Right.isoAppOf K
          (ModuleCat.derivedTensorBifunctorRightCompatible A K)
          (RHom.Unit.single (A := A))).hom ≫
        (P.singleBifunctorLeftUnitIso hn s).hom.app K =
      (P.single0LeftDerivedTensorIso s K).hom :=
  RHom.Unit.bifunctorLeftUnitIso_agrees_hom P.tensorModel hn s K

/-- Inverse agreement between bundled bifunctor and fixed-left comparisons. -/
@[simp, stacks 0E1U "inverse bundled bifunctor and fixed-left unit agreement"]
theorem singleBifunctorLeftUnitIso_agrees_inv
    (P : RHom.ClosedComparison (A := A))
    (hn : RHom.Unit.BifunctorComparisonIsNatural P.tensorModel)
    (s : RHom.Unit.single (A := A) ≅ 𝟙_ (DerivedCategory (ModuleCat.{u} A)))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (P.singleBifunctorLeftUnitIso hn s).inv.app K ≫
        (DerivedTensor.Bifunctor.Right.isoAppOf K
          (ModuleCat.derivedTensorBifunctorRightCompatible A K)
          (RHom.Unit.single (A := A))).inv =
      (P.single0LeftDerivedTensorIso s K).inv :=
  RHom.Unit.bifunctorLeftUnitIso_agrees_inv P.tensorModel hn s K

end Bifunctor

end CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison
