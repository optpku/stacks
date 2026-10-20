/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Cohomology.Noetherian
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.ToUnbounded
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Bidual
public import Mathlib.Algebra.Category.FGModuleCat.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
variable [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
variable (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
variable (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsDualizingComplex H)

include hω

/-- Derived internal Hom into a dualizing complex preserves finite cohomology. -/
theorem coherentDualityObjMem
    (K : (D[ModuleCat.isFG A])ᵒᵖ) :
    DerivedCategory.cohomologyIn (ModuleCat.isFG A)
      ((((DerivedCategory.cohomologyIn (ModuleCat.isFG A)).ι.op ⋙
        (RightInternalHom.ofBraidedClosedOf H).dualFunctor ω).obj K)) := sorry

/-- Derived internal Hom into `ω`, restricted to complexes with finite cohomology. -/
noncomputable def coherentDuality :
    (D[ModuleCat.isFG A])ᵒᵖ ⥤ D[ModuleCat.isFG A] :=
  (DerivedCategory.cohomologyIn (ModuleCat.isFG A)).lift
    ((DerivedCategory.cohomologyIn (ModuleCat.isFG A)).ι.op ⋙
      (RightInternalHom.ofBraidedClosedOf H).dualFunctor ω)
    (coherentDualityObjMem H ω hω)

/-- The underlying object of `coherentDuality` is derived internal Hom into `ω`. -/
theorem coherentDuality_obj_obj (K : (D[ModuleCat.isFG A])ᵒᵖ) :
    ((coherentDuality H ω hω).obj K).obj =
      (MonoidalClosed.ihomOf H (Opposite.unop K).obj).obj ω := sorry

section PlusDuality

open Plus.CohomologyIn

/-- Derived internal Hom into a dualizing complex sends bounded-below coherent complexes to
bounded-above complexes. -/
theorem plusDualityObjBoundedAbove
    (K : (D⁺[ModuleCat.isFG A])ᵒᵖ) :
    (t.minus : ObjectProperty (DerivedCategory (ModuleCat.{u} A)))
      ((((ambient (ModuleCat.isFG A)).op ⋙
        (RightInternalHom.ofBraidedClosedOf H).dualFunctor ω).obj K)) := sorry

/-- The bounded-above image of a bounded-below coherent complex still has finite cohomology. -/
theorem plusDualityObjFinite
    (K : (D⁺[ModuleCat.isFG A])ᵒᵖ) :
    Minus.cohomologyIn (ModuleCat.isFG A)
      (((t.minus : ObjectProperty (DerivedCategory (ModuleCat.{u} A))).lift
        ((ambient (ModuleCat.isFG A)).op ⋙
          (RightInternalHom.ofBraidedClosedOf H).dualFunctor ω)
        (plusDualityObjBoundedAbove H ω hω)).obj K) := sorry

/-- Derived internal Hom into `ω`, from bounded-below to bounded-above coherent complexes. -/
noncomputable def plusDuality :
    (D⁺[ModuleCat.isFG A])ᵒᵖ ⥤ D⁻[ModuleCat.isFG A] :=
  (Minus.cohomologyIn (ModuleCat.isFG A)).lift
    ((t.minus : ObjectProperty (DerivedCategory (ModuleCat.{u} A))).lift
      ((ambient (ModuleCat.isFG A)).op ⋙
        (RightInternalHom.ofBraidedClosedOf H).dualFunctor ω)
      (plusDualityObjBoundedAbove H ω hω))
    (plusDualityObjFinite H ω hω)

/-- The ambient value of `plusDuality` is derived internal Hom into `ω`. -/
theorem plusDuality_obj_obj_obj (K : (D⁺[ModuleCat.isFG A])ᵒᵖ) :
    ((plusDuality H ω hω).obj K).obj.obj =
      (MonoidalClosed.ihomOf H (Opposite.unop K).obj.obj).obj ω := sorry

end PlusDuality

section BoundedDuality

open Bounded.CohomologyIn

/-- Derived internal Hom into a dualizing complex preserves bounded coherent complexes. -/
theorem boundedDualityObjBounded
    (K : (Dᵇ[ModuleCat.isFG A])ᵒᵖ) :
    (t.bounded : ObjectProperty (DerivedCategory (ModuleCat.{u} A)))
      ((((ambient (ModuleCat.isFG A)).op ⋙
        (RightInternalHom.ofBraidedClosedOf H).dualFunctor ω).obj K)) := sorry

/-- The bounded image of a bounded coherent complex still has finite cohomology. -/
theorem boundedDualityObjFinite
    (K : (Dᵇ[ModuleCat.isFG A])ᵒᵖ) :
    Bounded.cohomologyIn (ModuleCat.isFG A)
      (((t.bounded : ObjectProperty (DerivedCategory (ModuleCat.{u} A))).lift
        ((ambient (ModuleCat.isFG A)).op ⋙
          (RightInternalHom.ofBraidedClosedOf H).dualFunctor ω)
        (boundedDualityObjBounded H ω hω)).obj K) := sorry

/-- Derived internal Hom into `ω`, restricted to bounded coherent complexes. -/
noncomputable def boundedDuality :
    (Dᵇ[ModuleCat.isFG A])ᵒᵖ ⥤ Dᵇ[ModuleCat.isFG A] :=
  (Bounded.cohomologyIn (ModuleCat.isFG A)).lift
    ((t.bounded : ObjectProperty (DerivedCategory (ModuleCat.{u} A))).lift
      ((ambient (ModuleCat.isFG A)).op ⋙
        (RightInternalHom.ofBraidedClosedOf H).dualFunctor ω)
      (boundedDualityObjBounded H ω hω))
    (boundedDualityObjFinite H ω hω)

/-- The ambient value of `boundedDuality` is derived internal Hom into `ω`. -/
theorem boundedDuality_obj_obj_obj (K : (Dᵇ[ModuleCat.isFG A])ᵒᵖ) :
    ((boundedDuality H ω hω).obj K).obj.obj =
      (MonoidalClosed.ihomOf H (Opposite.unop K).obj.obj).obj ω := sorry

end BoundedDuality

/-- Naturality of the bidual map after restricting to complexes with finite cohomology. -/
theorem coherentBidualNaturality
    {K L : D[ModuleCat.isFG A]} (f : K ⟶ L) :
    f ≫ homMk ((RightInternalHom.ofBraidedClosedOf H).toBidualApp ω L.obj) =
      homMk ((RightInternalHom.ofBraidedClosedOf H).toBidualApp ω K.obj) ≫
        ((coherentDuality H ω hω).rightOp ⋙ coherentDuality H ω hω).map f := sorry

/-- The canonical bidual transformation on complexes with finite cohomology. -/
noncomputable def coherentBidual :
    𝟭 (D[ModuleCat.isFG A]) ⟶
      (coherentDuality H ω hω).rightOp ⋙ coherentDuality H ω hω where
  app K := homMk ((RightInternalHom.ofBraidedClosedOf H).toBidualApp ω K.obj)
  naturality _ _ f := coherentBidualNaturality H ω hω f

/-- The ambient component of `coherentBidual` is the canonical internal-Hom bidual map. -/
theorem coherentBidual_app_hom (K : D[ModuleCat.isFG A]) :
    ((coherentBidual H ω hω).app K).hom =
      (RightInternalHom.ofBraidedClosedOf H).toBidualApp ω K.obj := sorry

/-- The canonical coherent bidual transformation is an isomorphism. -/
theorem coherentBidual_isIso : IsIso (coherentBidual H ω hω) := sorry

/-- Derived internal Hom into a dualizing complex is an anti-equivalence on complexes with
finite cohomology. -/
theorem coherentDuality_isEquivalence :
    (coherentDuality H ω hω).IsEquivalence := sorry

/-- Derived internal Hom into a dualizing complex exchanges the bounded-below and bounded-above
categories of complexes with finite cohomology. -/
theorem plusDuality_isEquivalence :
    (plusDuality H ω hω).IsEquivalence := sorry

/-- Derived internal Hom into a dualizing complex is an anti-equivalence on bounded complexes
with finite cohomology. -/
theorem boundedDuality_isEquivalence :
    (boundedDuality H ω hω).IsEquivalence := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
