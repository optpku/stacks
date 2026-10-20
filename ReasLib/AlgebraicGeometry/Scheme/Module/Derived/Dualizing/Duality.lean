/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.Coherent
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Bidual

@[expose] public section
open CategoryTheory
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open scoped DerivedCategory.CohomologyIn
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.IsDualizingComplex
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
variable [BraidedCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
variable (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
variable (K : RingedSpace.ModuleDerived X.toRingedSpace)
variable (hK : IsDualizingComplex K)
include hK

/-- The cohomology of a dualizing complex is coherent. -/
theorem coherentCohomology :
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K := sorry

/-- Derived internal Hom into a dualizing complex preserves coherent cohomology. -/
theorem coherentDualityObjMem
    (L : (D[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])ᵒᵖ) :
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)
      ((((DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)).ι.op ⋙
        (RightInternalHom.ofBraidedClosedOf H).dualFunctor K).obj L)) := sorry

/-- Derived internal Hom into `K`, restricted to complexes with coherent cohomology. -/
noncomputable def coherentDuality :
    (D[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])ᵒᵖ ⥤
      D[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf] :=
  (DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)).lift
    ((DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)).ι.op ⋙
      (RightInternalHom.ofBraidedClosedOf H).dualFunctor K)
    (coherentDualityObjMem H K hK)

/-- The underlying object of `coherentDuality` is derived internal Hom into `K`. -/
theorem coherentDuality_obj_obj
    (L : (D[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])ᵒᵖ) :
    ((coherentDuality H K hK).obj L).obj =
      (MonoidalClosed.ihomOf H (Opposite.unop L).obj).obj K := sorry

/-- Derived internal Hom into a dualizing complex is an anti-equivalence of complexes with coherent cohomology. -/
theorem coherentDualityIsEquivalence :
    (coherentDuality H K hK).IsEquivalence := sorry

/-- Naturality of the bidual map after restricting to complexes with coherent cohomology. -/
theorem coherentBidualNaturality
    {L M : D[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]} (f : L ⟶ M) :
    f ≫ homMk ((RightInternalHom.ofBraidedClosedOf H).toBidualApp K M.obj) =
      homMk ((RightInternalHom.ofBraidedClosedOf H).toBidualApp K L.obj) ≫
        ((coherentDuality H K hK).rightOp ⋙ coherentDuality H K hK).map f := sorry

/-- The canonical bidual transformation on complexes with coherent cohomology. -/
noncomputable def coherentBidual :
    𝟭 (D[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]) ⟶
      (coherentDuality H K hK).rightOp ⋙ coherentDuality H K hK where
  app L := homMk ((RightInternalHom.ofBraidedClosedOf H).toBidualApp K L.obj)
  naturality _ _ f := coherentBidualNaturality H K hK f

/-- The ambient component of `coherentBidual` is the canonical internal-Hom bidual map. -/
theorem coherentBidual_app_hom
    (L : D[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf]) :
    ((coherentBidual H K hK).app L).hom =
      (RightInternalHom.ofBraidedClosedOf H).toBidualApp K L.obj := sorry

/-- The canonical bidual transformation is an isomorphism. -/
theorem coherentBidualIsIso : IsIso (coherentBidual H K hK) := sorry

section PlusDuality
variable [CompactSpace X]
open DerivedCategory.Plus.CohomologyIn

/-- Derived internal Hom into a dualizing complex sends bounded-below coherent complexes to bounded-above complexes. -/
theorem plusDualityObjBoundedAbove
    (L : (D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])ᵒᵖ) :
    (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))
      ((((ambient (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)).op ⋙
        (RightInternalHom.ofBraidedClosedOf H).dualFunctor K).obj L)) := sorry

/-- The bounded-above image of a bounded-below coherent complex has coherent cohomology. -/
theorem plusDualityObjCoherent
    (L : (D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])ᵒᵖ) :
    DerivedCategory.Minus.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)
      (((t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)).lift
        ((ambient (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)).op ⋙
          (RightInternalHom.ofBraidedClosedOf H).dualFunctor K)
        (plusDualityObjBoundedAbove H K hK)).obj L) := sorry

/-- Derived internal Hom into `K`, from bounded-below to bounded-above coherent complexes. -/
noncomputable def plusDuality :
    (D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])ᵒᵖ ⥤
      D⁻[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf] :=
  (DerivedCategory.Minus.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)).lift
    ((t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)).lift
      ((ambient (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)).op ⋙
        (RightInternalHom.ofBraidedClosedOf H).dualFunctor K)
      (plusDualityObjBoundedAbove H K hK))
    (plusDualityObjCoherent H K hK)

/-- The ambient value of `plusDuality` is derived internal Hom into `K`. -/
theorem plusDuality_obj_obj_obj
    (L : (D⁺[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])ᵒᵖ) :
    ((plusDuality H K hK).obj L).obj.obj =
      (MonoidalClosed.ihomOf H (Opposite.unop L).obj.obj).obj K := sorry

/-- On a quasi-compact scheme, this duality exchanges bounded-below and bounded-above coherent complexes. -/
theorem plusDualityIsEquivalence :
    (plusDuality H K hK).IsEquivalence := sorry
end PlusDuality

section BoundedDuality
variable [CompactSpace X]
open DerivedCategory.Bounded.CohomologyIn

/-- Derived internal Hom into a dualizing complex preserves bounded complexes. -/
theorem boundedDualityObjBounded
    (L : (Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])ᵒᵖ) :
    (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))
      ((((ambient (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)).op ⋙
        (RightInternalHom.ofBraidedClosedOf H).dualFunctor K).obj L)) := sorry

/-- The bounded image of a bounded coherent complex still has coherent cohomology. -/
theorem boundedDualityObjCoherent
    (L : (Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])ᵒᵖ) :
    DerivedCategory.Bounded.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)
      (((t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)).lift
        ((ambient (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)).op ⋙
          (RightInternalHom.ofBraidedClosedOf H).dualFunctor K)
        (boundedDualityObjBounded H K hK)).obj L) := sorry

/-- Derived internal Hom into `K`, restricted to bounded complexes with coherent cohomology. -/
noncomputable def boundedDuality :
    (Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])ᵒᵖ ⥤
      Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf] :=
  (DerivedCategory.Bounded.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)).lift
    ((t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)).lift
      ((ambient (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)).op ⋙
        (RightInternalHom.ofBraidedClosedOf H).dualFunctor K)
      (boundedDualityObjBounded H K hK))
    (boundedDualityObjCoherent H K hK)

/-- The ambient value of `boundedDuality` is derived internal Hom into `K`. -/
theorem boundedDuality_obj_obj_obj
    (L : (Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])ᵒᵖ) :
    ((boundedDuality H K hK).obj L).obj.obj =
      (MonoidalClosed.ihomOf H (Opposite.unop L).obj.obj).obj K := sorry

/-- On a quasi-compact scheme, this duality is an anti-equivalence on bounded coherent complexes. -/
theorem boundedDualityIsEquivalence :
    (boundedDuality H K hK).IsEquivalence := sorry
end BoundedDuality
end AlgebraicGeometry.Scheme.IsDualizingComplex
