/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Forget
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.BaseChange
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Resize

/-!
# Base change of coherent sheaves along a morphism of bases

For `g : B' ⟶ B` of algebraic spaces, the pasting isomorphism
`(X ×_B B') ×_{B'} T ≅ X ×_B T` transports finitely presented flat modules
with proper support, yielding a functor `Obj (pullback.snd f g) ⥤ Obj f`.
-/

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open CategoryTheory.Limits CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B B' : AlgebraicSpace S}

/-- The canonical identification `(X ×_B B') ×_{B'} T ≅ X ×_B T`. -/
@[expose]
def fiberIso (f : X ⟶ B) (g : B' ⟶ B) (σ : SchemesOver B') :
    fiber (pullback.snd f g) σ ≅ fiber f ((CostructuredArrow.map g).obj σ) :=
  pullbackLeftPullbackSndIso f g σ.hom

/-- The first projection of `fiberIso.hom` is the composite of the projections to `X`. -/
@[expose]
def fiberIso_fst (f : X ⟶ B) (g : B' ⟶ B) (σ : SchemesOver B') :
    (fiberIso f g σ).hom ≫ pullback.fst f ((CostructuredArrow.map g).obj σ).hom =
      pullback.fst (pullback.snd f g) σ.hom ≫ pullback.fst f g :=
  pullbackLeftPullbackSndIso_hom_fst f g σ.hom

/-- The second projection of `fiberIso.hom` recovers the projection to `T`. -/
@[expose]
def fiberIso_snd (f : X ⟶ B) (g : B' ⟶ B) (σ : SchemesOver B') :
    (fiberIso f g σ).hom ≫ pullback.snd f ((CostructuredArrow.map g).obj σ).hom =
      pullback.snd (pullback.snd f g) σ.hom :=
  pullbackLeftPullbackSndIso_hom_snd f g σ.hom

/-- First-projection comparison for the pasting naturality square. -/
private def fiberIsoNaturalityFst (f : X ⟶ B) (g : B' ⟶ B) {σ τ : SchemesOver B'} (h : σ ⟶ τ) :
    (fiberMap (pullback.snd f g) h ≫ (fiberIso f g τ).hom) ≫
        pullback.fst f ((CostructuredArrow.map g).obj τ).hom =
      ((fiberIso f g σ).hom ≫ fiberMap f ((CostructuredArrow.map g).map h)) ≫
        pullback.fst f ((CostructuredArrow.map g).obj τ).hom :=
  (((Category.assoc _ _ _).trans
        (congrArg (fun k => fiberMap (pullback.snd f g) h ≫ k) (fiberIso_fst f g τ))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ pullback.fst f g)
          (fiberMap_fst (pullback.snd f g) h)))).trans
    ((((Category.assoc _ _ _).trans
          (congrArg (fun k => (fiberIso f g σ).hom ≫ k)
            (fiberMap_fst f ((CostructuredArrow.map g).map h)))).trans
        (fiberIso_fst f g σ)).symm)

/-- Second-projection comparison for the pasting naturality square. -/
private def fiberIsoNaturalitySnd (f : X ⟶ B) (g : B' ⟶ B) {σ τ : SchemesOver B'} (h : σ ⟶ τ) :
    (fiberMap (pullback.snd f g) h ≫ (fiberIso f g τ).hom) ≫
        pullback.snd f ((CostructuredArrow.map g).obj τ).hom =
      ((fiberIso f g σ).hom ≫ fiberMap f ((CostructuredArrow.map g).map h)) ≫
        pullback.snd f ((CostructuredArrow.map g).obj τ).hom :=
  (((Category.assoc _ _ _).trans
        (congrArg (fun k => fiberMap (pullback.snd f g) h ≫ k) (fiberIso_snd f g τ))).trans
      (fiberMap_snd (pullback.snd f g) h)).trans
    ((((Category.assoc _ _ _).trans
          (congrArg (fun k => (fiberIso f g σ).hom ≫ k)
            (fiberMap_snd f ((CostructuredArrow.map g).map h)))).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ (ofOverFunctor S).map h.left)
            (fiberIso_snd f g σ)))).symm)

/-- Fibre maps after changing the base commute with the pasting identification. -/
def fiberIso_natural (f : X ⟶ B) (g : B' ⟶ B) {σ τ : SchemesOver B'} (h : σ ⟶ τ) :
    fiberMap (pullback.snd f g) h ≫ (fiberIso f g τ).hom =
      (fiberIso f g σ).hom ≫ fiberMap f ((CostructuredArrow.map g).map h) :=
  pullback.hom_ext (fiberIsoNaturalityFst f g h) (fiberIsoNaturalitySnd f g h)

/-- The inverse form of `fiberIso_natural`, matching successive module pullbacks. -/
@[expose]
def fiberIso_natural_inv (f : X ⟶ B) (g : B' ⟶ B) {σ τ : SchemesOver B'} (h : σ ⟶ τ) :
    fiberMap f ((CostructuredArrow.map g).map h) ≫ (fiberIso f g τ).inv =
      (fiberIso f g σ).inv ≫ fiberMap (pullback.snd f g) h :=
  (Iso.comp_inv_eq (fiberIso f g τ)).mpr
    (((Category.assoc (fiberIso f g σ).inv (fiberMap (pullback.snd f g) h)
          (fiberIso f g τ).hom).trans
        (congrArg (fun k => (fiberIso f g σ).inv ≫ k) (fiberIso_natural f g h))).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ fiberMap f ((CostructuredArrow.map g).map h))
            (Iso.inv_hom_id (fiberIso f g σ))).trans
          (Category.id_comp _)))).symm

/-- The module on `X_T` obtained by transporting a module on `X'_T` along `fiberIso`. -/
@[expose]
def baseChangeModule (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    (x : Obj (pullback.snd f g)) :
    (fiber f ((CostructuredArrow.map g).obj x.σ)).Modules :=
  (Modules.pullback (fiberIso f g x.σ).inv).obj x.module

/-- Finite presentation is preserved by transport along `fiberIso`. -/
theorem baseChangeModule_isFinitePresentation (f : X ⟶ B) (g : B' ⟶ B)
    [FinitePresentation f] (x : Obj (pullback.snd f g)) :
    (baseChangeModule f g x).IsFinitePresentation := sorry

/-- Proper support over the test scheme is preserved by transport along `fiberIso`. -/
theorem baseChangeModule_hasProperSupportOver (f : X ⟶ B) (g : B' ⟶ B)
    [FinitePresentation f] (x : Obj (pullback.snd f g)) :
    Modules.HasProperSupportOver (fiberToBase f ((CostructuredArrow.map g).obj x.σ))
      (baseChangeModule f g x) := sorry

/-- Relative flatness is preserved by transport along `fiberIso`. -/
theorem flatOver_baseChangeModule (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    (x : Obj (pullback.snd f g)) :
    flatOver (baseChangeModule f g x)
      (fiberToBase f ((CostructuredArrow.map g).obj x.σ)) := sorry

/-- The object of `Obj f` obtained by viewing `(T, g', F)` over `B'` as a triple over `B`. -/
@[expose]
def baseChangeObj (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    (x : Obj (pullback.snd f g)) : Obj f :=
  { σ := (CostructuredArrow.map g).obj x.σ
    module := baseChangeModule f g x
    isFinitePresentation := baseChangeModule_isFinitePresentation f g x
    isFlat := flatOver_baseChangeModule f g x
    hasProperSupport := baseChangeModule_hasProperSupportOver f g x }

/-- Reassociation of module pullback along `fiberMap` and `fiberIso.inv`. -/
private def baseChangeMapIsoReassoc (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    {x y : Obj (pullback.snd f g)} (α : x ⟶ y) :
    (Modules.pullback (fiberMap f ((CostructuredArrow.map g).map α.base))).obj
        (baseChangeModule f g y) ≅
      (Modules.pullback
          (fiberMap f ((CostructuredArrow.map g).map α.base) ≫
            (fiberIso f g y.σ).inv)).obj y.module :=
  (Modules.pullbackCompIso (fiberMap f ((CostructuredArrow.map g).map α.base))
      (fiberIso f g y.σ).inv).app y.module

/-- Transport of the pulled-back module along the pasting naturality equality. -/
private def baseChangeMapIsoPath (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    {x y : Obj (pullback.snd f g)} (α : x ⟶ y) :
    (Modules.pullback
        (fiberMap f ((CostructuredArrow.map g).map α.base) ≫ (fiberIso f g y.σ).inv)).obj
      y.module ≅
      (Modules.pullback
          ((fiberIso f g x.σ).inv ≫ fiberMap (pullback.snd f g) α.base)).obj y.module :=
  eqToIso (congrArg (fun k => (Modules.pullback k).obj y.module)
    (fiberIso_natural_inv f g α.base))

/-- Reassociation of module pullback along `fiberIso.inv` and the fibre map of `α`. -/
private def baseChangeMapIsoReassocInv (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    {x y : Obj (pullback.snd f g)} (α : x ⟶ y) :
    (Modules.pullback
        ((fiberIso f g x.σ).inv ≫ fiberMap (pullback.snd f g) α.base)).obj y.module ≅
      (Modules.pullback (fiberIso f g x.σ).inv).obj
        ((Modules.pullback (fiberMap (pullback.snd f g) α.base)).obj y.module) :=
  (Modules.pullbackCompIso (fiberIso f g x.σ).inv
      (fiberMap (pullback.snd f g) α.base)).symm.app y.module

/-- The module isomorphism of `baseChange` on a morphism, transporting `α.iso` along
`fiberIso`. -/
def baseChangeMapIso (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    {x y : Obj (pullback.snd f g)} (α : x ⟶ y) :
    (Modules.pullback (fiberMap f ((CostructuredArrow.map g).map α.base))).obj
        (baseChangeModule f g y) ≅
      baseChangeModule f g x :=
  baseChangeMapIsoReassoc f g α ≪≫
    baseChangeMapIsoPath f g α ≪≫
    baseChangeMapIsoReassocInv f g α ≪≫
    (Modules.pullback (fiberIso f g x.σ).inv).mapIso α.iso

/-- The morphism obtained by composing its base map with `g` and transporting its module isomorphism. -/
@[expose]
def baseChangeHom (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    {x y : Obj (pullback.snd f g)} (α : x ⟶ y) :
    baseChangeObj f g x ⟶ baseChangeObj f g y :=
  homMk ((CostructuredArrow.map g).map α.base) (baseChangeMapIso f g α)

/-- Transport of coherent-sheaf morphisms along the change of base preserves identities. -/
theorem baseChangeHom_id (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    (x : Obj (pullback.snd f g)) :
    baseChangeHom f g (𝟙 x) = 𝟙 (baseChangeObj f g x) := sorry

/-- Transport of coherent-sheaf morphisms along the change of base preserves composition. -/
theorem baseChangeHom_comp (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    {x y z : Obj (pullback.snd f g)} (α : x ⟶ y) (β : y ⟶ z) :
    baseChangeHom f g (α ≫ β) = baseChangeHom f g α ≫ baseChangeHom f g β := sorry

/-- The functor `Coh_{X'/B'} ⥤ Coh_{X/B}` induced by `g : B' ⟶ B`, with
`X' = X ×_B B'` and `f' = pullback.snd f g`. -/
@[expose]
def baseChange (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f] :
    Obj (pullback.snd f g) ⥤ Obj f where
  obj x := baseChangeObj f g x
  map α := baseChangeHom f g α
  map_id := baseChangeHom_id f g
  map_comp := baseChangeHom_comp f g

/-- On objects, `baseChange` sends the test scheme over `B'` to its image under
`CostructuredArrow.map g`. -/
theorem baseChange_obj_σ (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    (x : Obj (pullback.snd f g)) :
    ((baseChange f g).obj x).σ = (CostructuredArrow.map g).obj x.σ := sorry

/-- On objects, `baseChange` transports the module along `fiberIso.inv`. -/
theorem baseChange_obj_module (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    (x : Obj (pullback.snd f g)) :
    ((baseChange f g).obj x).module = baseChangeModule f g x := sorry

/-- The commutative square of coherent-sheaf categories and schemes over the bases,
with apex `Coh_{X ×_B B'/B'}` and lower edge `Sch/B' ⥤ Sch/B`. -/
@[expose]
def square (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f] :
    CatCommSqOver (toSchemesOver f) (CostructuredArrow.map g) (Obj (pullback.snd f g)) where
  fst := baseChange f g
  snd := toSchemesOver (pullback.snd f g)
  iso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {_ _} _ ↦ rfl)

/-- The square of coherent-sheaf categories induced by any change of algebraic-space base
is a 2-fibre product square. -/
instance square.instIsBilimit (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f] :
    CatCommSqOver.Resized.IsBilimit (square f g) := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
