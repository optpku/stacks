module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import stacks_project.Chap67.Lemma_67_28_3_Pullback
public import stacks_project.Chap99.Situation_99_5_1_Category

/-!
# Base change of coherent sheaves along a morphism of bases

For `g : B' ⟶ B` of algebraic spaces, the pasting isomorphism
`(X ×_B B') ×_{B'} T ≅ X ×_B T` transports finitely presented flat modules
with proper support, yielding a functor `Obj (pullback.snd f g) ⥤ Obj f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B B' : AlgebraicSpace S}

/-- Viewing a scheme `T` over `B'` as a scheme over `B` via `T ⟶ B' ⟶ B` composes
the structure morphism with `g`. -/
theorem changeBase_hom (g : B' ⟶ B) (σ : SchemesOver B') :
    ((CostructuredArrow.map g).obj σ).hom = σ.hom ≫ g :=
  rfl

/-- The first projection of `fiberMap` is the projection to `X`. -/
def fiberMap_comp_fst (f : X ⟶ B) {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    fiberMap f h ≫ pullback.fst f τ.hom = pullback.fst f σ.hom :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The second projection of `fiberMap` is the projection to the varying base. -/
def fiberMap_comp_snd (f : X ⟶ B) {σ τ : SchemesOver B} (h : σ ⟶ τ) :
    fiberMap f h ≫ pullback.snd f τ.hom =
      pullback.snd f σ.hom ≫ (ofOverFunctor S).map h.left :=
  pullback.lift_snd _ _ _

/-- The canonical identification `(X ×_B B') ×_{B'} T ≅ X ×_B T`. -/
def fiberIso (f : X ⟶ B) (g : B' ⟶ B) (σ : SchemesOver B') :
    fiber (pullback.snd f g) σ ≅ fiber f ((CostructuredArrow.map g).obj σ) :=
  pullbackLeftPullbackSndIso f g σ.hom

/-- The first projection of `fiberIso.hom` is the composite of the projections to `X`. -/
def fiberIso_fst (f : X ⟶ B) (g : B' ⟶ B) (σ : SchemesOver B') :
    (fiberIso f g σ).hom ≫ pullback.fst f ((CostructuredArrow.map g).obj σ).hom =
      pullback.fst (pullback.snd f g) σ.hom ≫ pullback.fst f g :=
  pullbackLeftPullbackSndIso_hom_fst f g σ.hom

/-- The second projection of `fiberIso.hom` recovers the projection to `T`. -/
def fiberIso_snd (f : X ⟶ B) (g : B' ⟶ B) (σ : SchemesOver B') :
    (fiberIso f g σ).hom ≫ pullback.snd f ((CostructuredArrow.map g).obj σ).hom =
      pullback.snd (pullback.snd f g) σ.hom :=
  pullbackLeftPullbackSndIso_hom_snd f g σ.hom

/-- First-projection comparison for the pasting naturality square. -/
def fiberIso_natural_fst (f : X ⟶ B) (g : B' ⟶ B) {σ τ : SchemesOver B'} (h : σ ⟶ τ) :
    (fiberMap (pullback.snd f g) h ≫ (fiberIso f g τ).hom) ≫
        pullback.fst f ((CostructuredArrow.map g).obj τ).hom =
      ((fiberIso f g σ).hom ≫ fiberMap f ((CostructuredArrow.map g).map h)) ≫
        pullback.fst f ((CostructuredArrow.map g).obj τ).hom :=
  (((Category.assoc _ _ _).trans
        (congrArg (fun k => fiberMap (pullback.snd f g) h ≫ k) (fiberIso_fst f g τ))).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ pullback.fst f g)
          (fiberMap_comp_fst (pullback.snd f g) h)))).trans
    ((((Category.assoc _ _ _).trans
          (congrArg (fun k => (fiberIso f g σ).hom ≫ k)
            (fiberMap_comp_fst f ((CostructuredArrow.map g).map h)))).trans
        (fiberIso_fst f g σ)).symm)

/-- Second-projection comparison for the pasting naturality square. -/
def fiberIso_natural_snd (f : X ⟶ B) (g : B' ⟶ B) {σ τ : SchemesOver B'} (h : σ ⟶ τ) :
    (fiberMap (pullback.snd f g) h ≫ (fiberIso f g τ).hom) ≫
        pullback.snd f ((CostructuredArrow.map g).obj τ).hom =
      ((fiberIso f g σ).hom ≫ fiberMap f ((CostructuredArrow.map g).map h)) ≫
        pullback.snd f ((CostructuredArrow.map g).obj τ).hom :=
  (((Category.assoc _ _ _).trans
        (congrArg (fun k => fiberMap (pullback.snd f g) h ≫ k) (fiberIso_snd f g τ))).trans
      (fiberMap_comp_snd (pullback.snd f g) h)).trans
    ((((Category.assoc _ _ _).trans
          (congrArg (fun k => (fiberIso f g σ).hom ≫ k)
            (fiberMap_comp_snd f ((CostructuredArrow.map g).map h)))).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ (ofOverFunctor S).map h.left)
            (fiberIso_snd f g σ)))).symm)

/-- Fibre maps after changing the base commute with the pasting identification. -/
def fiberIso_natural (f : X ⟶ B) (g : B' ⟶ B) {σ τ : SchemesOver B'} (h : σ ⟶ τ) :
    fiberMap (pullback.snd f g) h ≫ (fiberIso f g τ).hom =
      (fiberIso f g σ).hom ≫ fiberMap f ((CostructuredArrow.map g).map h) :=
  pullback.hom_ext (fiberIso_natural_fst f g h) (fiberIso_natural_snd f g h)

/-- The inverse form of `fiberIso_natural`, matching successive module pullbacks. -/
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
def baseChangeModule (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    (x : Obj (pullback.snd f g)) :
    (fiber f ((CostructuredArrow.map g).obj x.σ)).Modules :=
  (Modules.pullback (fiberIso f g x.σ).inv).obj x.module

/-- Finite presentation is preserved by transport along `fiberIso`. -/
instance instIsFinitePresentation_baseChangeModule (f : X ⟶ B) (g : B' ⟶ B)
    [FinitePresentation f] (x : Obj (pullback.snd f g)) :
    (baseChangeModule f g x).IsFinitePresentation :=
  sorry

/-- Proper support over the test scheme is preserved by transport along `fiberIso`. -/
instance instHasProperSupportOver_baseChangeModule (f : X ⟶ B) (g : B' ⟶ B)
    [FinitePresentation f] (x : Obj (pullback.snd f g)) :
    Modules.HasProperSupportOver (fiberToBase f ((CostructuredArrow.map g).obj x.σ))
      (baseChangeModule f g x) :=
  sorry

/-- Relative flatness is preserved by transport along `fiberIso`. -/
theorem flatOver_baseChangeModule (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    (x : Obj (pullback.snd f g)) :
    flatOver (baseChangeModule f g x)
      (fiberToBase f ((CostructuredArrow.map g).obj x.σ)) :=
  sorry

/-- The object of `Obj f` obtained by viewing `(T, g', F)` over `B'` as a triple over `B`. -/
def baseChangeObj (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    (x : Obj (pullback.snd f g)) : Obj f :=
  Obj.of ((CostructuredArrow.map g).obj x.σ) (baseChangeModule f g x)
    (flatOver_baseChangeModule f g x)

/-- Reassociation of module pullback along `fiberMap` and `fiberIso.inv`. -/
def baseChangeMapIso_reassoc (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    {x y : Obj (pullback.snd f g)} (α : x ⟶ y) :
    (Modules.pullback (fiberMap f ((CostructuredArrow.map g).map α.base))).obj
        (baseChangeModule f g y) ≅
      (Modules.pullback
          (fiberMap f ((CostructuredArrow.map g).map α.base) ≫
            (fiberIso f g y.σ).inv)).obj y.module :=
  (Modules.pullbackCompIso (fiberMap f ((CostructuredArrow.map g).map α.base))
      (fiberIso f g y.σ).inv).app y.module

/-- Transport of the pulled-back module along the pasting naturality equality. -/
def baseChangeMapIso_path (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    {x y : Obj (pullback.snd f g)} (α : x ⟶ y) :
    (Modules.pullback
        (fiberMap f ((CostructuredArrow.map g).map α.base) ≫ (fiberIso f g y.σ).inv)).obj
      y.module ≅
      (Modules.pullback
          ((fiberIso f g x.σ).inv ≫ fiberMap (pullback.snd f g) α.base)).obj y.module where
  hom :=
    eqToHom (congrArg (fun k => (Modules.pullback k).obj y.module)
      (fiberIso_natural_inv f g α.base))
  inv :=
    eqToHom (congrArg (fun k => (Modules.pullback k).obj y.module)
      (fiberIso_natural_inv f g α.base).symm)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Reassociation of module pullback along `fiberIso.inv` and the fibre map of `α`. -/
def baseChangeMapIso_reassoc' (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
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
  baseChangeMapIso_reassoc f g α ≪≫
    baseChangeMapIso_path f g α ≪≫
    baseChangeMapIso_reassoc' f g α ≪≫
    (Modules.pullback (fiberIso f g x.σ).inv).mapIso α.iso

/-- The functor `Coh_{X'/B'} ⥤ Coh_{X/B}` induced by `g : B' ⟶ B`, with
`X' = X ×_B B'` and `f' = pullback.snd f g`. -/
def baseChange (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f] :
    Obj (pullback.snd f g) ⥤ Obj f where
  obj x := baseChangeObj f g x
  map α := homMk ((CostructuredArrow.map g).map α.base) (baseChangeMapIso f g α)
  map_id := sorry
  map_comp := sorry

/-- On objects, `baseChange` sends the test scheme over `B'` to its image under
`CostructuredArrow.map g`. -/
theorem baseChange_obj_σ (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    (x : Obj (pullback.snd f g)) :
    ((baseChange f g).obj x).σ = (CostructuredArrow.map g).obj x.σ :=
  sorry

/-- On objects, `baseChange` transports the module along `fiberIso.inv`. -/
theorem baseChange_obj_module (f : X ⟶ B) (g : B' ⟶ B) [FinitePresentation f]
    (x : Obj (pullback.snd f g)) :
    ((baseChange f g).obj x).module = baseChangeModule f g x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
