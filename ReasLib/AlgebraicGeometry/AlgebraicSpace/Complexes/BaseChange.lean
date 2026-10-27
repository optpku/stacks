/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.StructureMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.BaseChange
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Resize.Basic

/-!
# Base change of admissible complexes

The pasting identification of fibres transports relatively perfect complexes
with fibrewise vanishing negative self-Ext through an arbitrary change of base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B B' : AlgebraicSpace S}

/-- First-projection comparison for the pasting naturality square. -/
private def fiberIsoNaturalityFst (f : X ⟶ B) (g : B' ⟶ B) {σ τ : SchemeOver B'} (h : σ ⟶ τ) :
    (CohStack.fiberMap (pullback.snd f g) h ≫ (pullbackLeftPullbackSndIso f g τ.hom).hom) ≫
        pullback.fst f ((CostructuredArrow.map g).obj τ).hom =
      ((pullbackLeftPullbackSndIso f g σ.hom).hom ≫ CohStack.fiberMap f ((CostructuredArrow.map g).map h)) ≫
        pullback.fst f ((CostructuredArrow.map g).obj τ).hom :=
  (((Category.assoc _ _ _).trans
        (congrArg (fun k => CohStack.fiberMap (pullback.snd f g) h ≫ k)
          (pullbackLeftPullbackSndIso_hom_fst f g τ.hom))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ pullback.fst f g)
          (CohStack.fiberMap_fst (pullback.snd f g) h)))).trans
    ((((Category.assoc _ _ _).trans
          (congrArg (fun k => (pullbackLeftPullbackSndIso f g σ.hom).hom ≫ k)
            (CohStack.fiberMap_fst f ((CostructuredArrow.map g).map h)))).trans
        (pullbackLeftPullbackSndIso_hom_fst f g σ.hom)).symm)

/-- Second-projection comparison for the pasting naturality square. -/
private def fiberIsoNaturalitySnd (f : X ⟶ B) (g : B' ⟶ B) {σ τ : SchemeOver B'} (h : σ ⟶ τ) :
    (CohStack.fiberMap (pullback.snd f g) h ≫ (pullbackLeftPullbackSndIso f g τ.hom).hom) ≫
        pullback.snd f ((CostructuredArrow.map g).obj τ).hom =
      ((pullbackLeftPullbackSndIso f g σ.hom).hom ≫ CohStack.fiberMap f ((CostructuredArrow.map g).map h)) ≫
        pullback.snd f ((CostructuredArrow.map g).obj τ).hom :=
  (((Category.assoc _ _ _).trans
        (congrArg (fun k => CohStack.fiberMap (pullback.snd f g) h ≫ k)
          (pullbackLeftPullbackSndIso_hom_snd f g τ.hom))).trans
      (CohStack.fiberMap_snd (pullback.snd f g) h)).trans
    ((((Category.assoc _ _ _).trans
          (congrArg (fun k => (pullbackLeftPullbackSndIso f g σ.hom).hom ≫ k)
            (CohStack.fiberMap_snd f ((CostructuredArrow.map g).map h)))).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ (ofOverFunctor S).map h.left)
            (pullbackLeftPullbackSndIso_hom_snd f g σ.hom)))).symm)

/-- Fibre maps after changing the base commute with the pasting identification. -/
private def fiberIsoNaturality (f : X ⟶ B) (g : B' ⟶ B) {σ τ : SchemeOver B'} (h : σ ⟶ τ) :
    CohStack.fiberMap (pullback.snd f g) h ≫ (pullbackLeftPullbackSndIso f g τ.hom).hom =
      (pullbackLeftPullbackSndIso f g σ.hom).hom ≫ CohStack.fiberMap f ((CostructuredArrow.map g).map h) :=
  pullback.hom_ext (fiberIsoNaturalityFst f g h) (fiberIsoNaturalitySnd f g h)

/-- Inverse pasting identifications commute with the induced fibre maps. -/
private def fiberIsoNaturalityInv (f : X ⟶ B) (g : B' ⟶ B) {σ τ : SchemeOver B'} (h : σ ⟶ τ) :
    CohStack.fiberMap f ((CostructuredArrow.map g).map h) ≫ (pullbackLeftPullbackSndIso f g τ.hom).inv =
      (pullbackLeftPullbackSndIso f g σ.hom).inv ≫ CohStack.fiberMap (pullback.snd f g) h :=
  (Iso.comp_inv_eq (pullbackLeftPullbackSndIso f g τ.hom)).mpr
    (((Category.assoc (pullbackLeftPullbackSndIso f g σ.hom).inv (CohStack.fiberMap (pullback.snd f g) h)
          (pullbackLeftPullbackSndIso f g τ.hom).hom).trans
        (congrArg (fun k => (pullbackLeftPullbackSndIso f g σ.hom).inv ≫ k)
          (fiberIsoNaturality f g h))).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ CohStack.fiberMap f ((CostructuredArrow.map g).map h))
            (Iso.inv_hom_id (pullbackLeftPullbackSndIso f g σ.hom))).trans
          (Category.id_comp _)))).symm

/-- The complex transported to the original family by derived pullback along the
inverse pasting identification. -/
def baseChangeComplex (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f]
    (x : category (pullback.snd f g)) :
    ModuleDerived (pullback f ((CostructuredArrow.map g).obj x.σ).hom) :=
  (ModuleDerived.pullback (pullbackLeftPullbackSndIso f g x.σ.hom).inv).obj x.complex

/-- Relative perfectness is preserved by the pasting identification of fibres. -/
theorem isPerfectRelative_baseChangeComplex (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] (x : category (pullback.snd f g)) :
    ModuleDerived.IsPerfectRelativeTo
      (pullback.snd f ((CostructuredArrow.map g).obj x.σ).hom)
      (baseChangeComplex f g x) := sorry

/-- Fibrewise negative self-Ext vanishing is preserved by the pasting identification of fibres. -/
theorem fiberNegativeSelfExtVanish_baseChangeComplex (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] (x : category (pullback.snd f g)) :
    ∀ t : FieldValuedPoint (ofOver ((CostructuredArrow.map g).obj x.σ).left),
      ModuleDerived.fiberNegativeExtVanish
        (pullback.snd f ((CostructuredArrow.map g).obj x.σ).hom)
        (baseChangeComplex f g x) (baseChangeComplex f g x) t := sorry

/-- The object of `category f` obtained by viewing `(T, g', E)` over `B'` as a triple over `B`. -/
def baseChangeObj (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f]
    (x : category (pullback.snd f g)) : category f :=
  Object.of ((CostructuredArrow.map g).obj x.σ) (baseChangeComplex f g x)
    (isPerfectRelative_baseChangeComplex f g x) (fiberNegativeSelfExtVanish_baseChangeComplex f g x)

/-- Derived pullback along a fibre map and an inverse pasting identification
reassociates canonically. -/
private def baseChangeMapIsoReassoc (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : category (pullback.snd f g)} (α : x ⟶ y) :
    (ModuleDerived.pullback (CohStack.fiberMap f ((CostructuredArrow.map g).map α.base))).obj
        (baseChangeComplex f g y) ≅
      (ModuleDerived.pullback
          (CohStack.fiberMap f ((CostructuredArrow.map g).map α.base) ≫
            (pullbackLeftPullbackSndIso f g y.σ.hom).inv)).obj y.complex :=
  (ModuleDerived.pullbackCompIso (CohStack.fiberMap f ((CostructuredArrow.map g).map α.base))
      (pullbackLeftPullbackSndIso f g y.σ.hom).inv).app y.complex

/-- Transport of the pulled-back complex along the pasting naturality equality. -/
private def baseChangeMapIsoPath (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : category (pullback.snd f g)} (α : x ⟶ y) :
    (ModuleDerived.pullback
        (CohStack.fiberMap f ((CostructuredArrow.map g).map α.base) ≫
          (pullbackLeftPullbackSndIso f g y.σ.hom).inv)).obj y.complex ≅
      (ModuleDerived.pullback
          ((pullbackLeftPullbackSndIso f g x.σ.hom).inv ≫
            CohStack.fiberMap (pullback.snd f g) α.base)).obj y.complex :=
  (ModuleDerived.pullbackCongr (fiberIsoNaturalityInv f g α.base)).app y.complex

/-- Derived pullback along an inverse pasting identification and a fibre map
reassociates canonically. -/
private def baseChangeMapIsoReassocInv (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : category (pullback.snd f g)} (α : x ⟶ y) :
    (ModuleDerived.pullback
        ((pullbackLeftPullbackSndIso f g x.σ.hom).inv ≫
            CohStack.fiberMap (pullback.snd f g) α.base)).obj y.complex ≅
      (ModuleDerived.pullback (pullbackLeftPullbackSndIso f g x.σ.hom).inv).obj
        ((ModuleDerived.pullback (CohStack.fiberMap (pullback.snd f g) α.base)).obj y.complex) :=
  (ModuleDerived.pullbackCompIso (pullbackLeftPullbackSndIso f g x.σ.hom).inv
      (CohStack.fiberMap (pullback.snd f g) α.base)).symm.app y.complex

/-- The derived isomorphism obtained by transporting a morphism through the pasting identifications. -/
@[no_expose]
def baseChangeMapIso (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : category (pullback.snd f g)} (α : x ⟶ y) :
    (ModuleDerived.pullback (CohStack.fiberMap f ((CostructuredArrow.map g).map α.base))).obj
        (baseChangeComplex f g y) ≅
      baseChangeComplex f g x :=
  baseChangeMapIsoReassoc f g α ≪≫
    baseChangeMapIsoPath f g α ≪≫
    baseChangeMapIsoReassocInv f g α ≪≫
    (ModuleDerived.pullback (pullbackLeftPullbackSndIso f g x.σ.hom).inv).mapIso α.iso

/-- The morphism obtained by changing the base of the supporting test scheme and
transporting the derived isomorphism through the pasting identifications. -/
def baseChangeHom (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : category (pullback.snd f g)} (α : x ⟶ y) :
    baseChangeObj f g x ⟶ baseChangeObj f g y :=
  Hom.of ((CostructuredArrow.map g).map α.base) (baseChangeMapIso f g α)

/-- Base change of morphisms preserves identities. -/
theorem baseChangeHom_id (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] (x : category (pullback.snd f g)) :
    baseChangeHom f g (𝟙 x) = 𝟙 (baseChangeObj f g x) := sorry

/-- Base change of morphisms preserves composition. -/
theorem baseChangeHom_comp (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f]
    {x y z : category (pullback.snd f g)} (α : x ⟶ y) (β : y ⟶ z) :
    baseChangeHom f g (α ≫ β) = baseChangeHom f g α ≫ baseChangeHom f g β := sorry

/-- The functor from admissible complexes on the changed family to admissible
complexes on the original family, induced by a morphism of bases. -/
def baseChange (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] :
    category (pullback.snd f g) ⥤ category f where
  obj x := baseChangeObj f g x
  map α := baseChangeHom f g α
  map_id := baseChangeHom_id f g
  map_comp := fun α β ↦ baseChangeHom_comp f g α β

/-- On objects, `baseChange` sends the test scheme over `B'` to its image under
`CostructuredArrow.map g`. -/
theorem baseChange_obj_σ (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] (x : category (pullback.snd f g)) :
    ((baseChange f g).obj x).σ = (CostructuredArrow.map g).obj x.σ := sorry

/-- The complex component of base change is the specified derived transport. -/
theorem baseChange_obj_complex (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] (x : category (pullback.snd f g)) :
    ((baseChange f g).obj x).complex = baseChangeComplex f g x := sorry

/-- The square comparing admissible complexes before and after a change of base,
with the canonical projections to schemes over the two bases. -/
def square (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] :
    CatCommSqOver (toSchemesOver f) (CostructuredArrow.map g)
      (category (pullback.snd f g)) where
  fst := baseChange f g
  snd := toSchemesOver (pullback.snd f g)
  iso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} _ ↦ rfl)

/-- The base-change square of admissible complexes is a universe-independent
2-fibre product square. -/
instance square.instIsBilimit (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] :
    CatCommSqOver.Resized.IsBilimit (square f g) := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
