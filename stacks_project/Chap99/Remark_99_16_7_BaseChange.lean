module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import stacks_project.Chap67.Lemma_67_28_3_Pullback
public import stacks_project.Chap67.Lemma_67_30_4_Pullback
public import stacks_project.Chap67.Lemma_67_40_3_Pullback
public import stacks_project.Chap99.Situation_99_16_3_Category

/-!
# Base change of admissible complexes along a morphism of bases

For `g : B' ⟶ B` of algebraic spaces, the pasting isomorphism
`(X ×_B B') ×_{B'} T ≅ X ×_B T` transports `T`-perfect complexes with fibrewise
negative self-Ext vanishing, yielding a functor `Obj (pullback.snd f g) ⥤ Obj f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Complexes
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} {X B B' : AlgebraicSpace S}

/-- Viewing a scheme `T` over `B'` as a scheme over `B` via `T ⟶ B' ⟶ B` composes
the structure morphism with `g`. -/
theorem changeBase_hom (g : B' ⟶ B) (σ : SchemeOver B') :
    ((CostructuredArrow.map g).obj σ).hom = σ.hom ≫ g :=
  sorry

/-- The canonical identification `(X ×_B B') ×_{B'} T ≅ X ×_B T`. -/
def fiberIso (f : X ⟶ B) (g : B' ⟶ B) (σ : SchemeOver B') :
    pullback (pullback.snd f g) σ.hom ≅ pullback f ((CostructuredArrow.map g).obj σ).hom :=
  pullbackLeftPullbackSndIso f g σ.hom

/-- The first projection of `fiberIso.hom` is the composite of the projections to `X`. -/
def fiberIso_fst (f : X ⟶ B) (g : B' ⟶ B) (σ : SchemeOver B') :
    (fiberIso f g σ).hom ≫ pullback.fst f ((CostructuredArrow.map g).obj σ).hom =
      pullback.fst (pullback.snd f g) σ.hom ≫ pullback.fst f g :=
  pullbackLeftPullbackSndIso_hom_fst f g σ.hom

/-- The second projection of `fiberIso.hom` recovers the projection to `T`. -/
def fiberIso_snd (f : X ⟶ B) (g : B' ⟶ B) (σ : SchemeOver B') :
    (fiberIso f g σ).hom ≫ pullback.snd f ((CostructuredArrow.map g).obj σ).hom =
      pullback.snd (pullback.snd f g) σ.hom :=
  pullbackLeftPullbackSndIso_hom_snd f g σ.hom

/-- First-projection comparison for the pasting naturality square. -/
def fiberIso_natural_fst (f : X ⟶ B) (g : B' ⟶ B) {σ τ : SchemeOver B'} (h : σ ⟶ τ) :
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
def fiberIso_natural_snd (f : X ⟶ B) (g : B' ⟶ B) {σ τ : SchemeOver B'} (h : σ ⟶ τ) :
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
def fiberIso_natural (f : X ⟶ B) (g : B' ⟶ B) {σ τ : SchemeOver B'} (h : σ ⟶ τ) :
    fiberMap (pullback.snd f g) h ≫ (fiberIso f g τ).hom =
      (fiberIso f g σ).hom ≫ fiberMap f ((CostructuredArrow.map g).map h) :=
  pullback.hom_ext (fiberIso_natural_fst f g h) (fiberIso_natural_snd f g h)

/-- The inverse form of `fiberIso_natural`, matching successive derived pullbacks. -/
def fiberIso_natural_inv (f : X ⟶ B) (g : B' ⟶ B) {σ τ : SchemeOver B'} (h : σ ⟶ τ) :
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

/-- The complex on `X_T` obtained by transporting a complex on `X'_T` along `fiberIso`. -/
def baseChangeComplex (f : X ⟶ B) (g : B' ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    (x : Obj (pullback.snd f g)) :
    ModuleDerived (pullback f ((CostructuredArrow.map g).obj x.σ).hom) :=
  (ModuleDerived.pullback (fiberIso f g x.σ).inv).obj x.complex

/-- Relative perfectness is preserved by transport along `fiberIso`. -/
theorem isPerfectRelative_baseChangeComplex (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] (x : Obj (pullback.snd f g)) :
    ModuleDerived.IsPerfectRelativeTo
      (pullback.snd f ((CostructuredArrow.map g).obj x.σ).hom)
      (baseChangeComplex f g x) :=
  sorry

/-- Fibrewise negative self-Ext vanishing is preserved by transport along `fiberIso`. -/
theorem fiberNegativeSelfExtVanish_baseChangeComplex (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] (x : Obj (pullback.snd f g)) :
    ∀ t : FieldValuedPoint (ofOver ((CostructuredArrow.map g).obj x.σ).left),
      ModuleDerived.fiberNegativeExtVanish
        (pullback.snd f ((CostructuredArrow.map g).obj x.σ).hom)
        (baseChangeComplex f g x) (baseChangeComplex f g x) t :=
  sorry

/-- The object of `Obj f` obtained by viewing `(T, g', E)` over `B'` as a triple over `B`. -/
def baseChangeObj (f : X ⟶ B) (g : B' ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    (x : Obj (pullback.snd f g)) : Obj f :=
  of ((CostructuredArrow.map g).obj x.σ) (baseChangeComplex f g x)
    (isPerfectRelative_baseChangeComplex f g x)
    (fiberNegativeSelfExtVanish_baseChangeComplex f g x)

/-- Reassociation of derived pullback along `fiberMap` and `fiberIso.inv`. -/
def baseChangeMapIso_reassoc (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : Obj (pullback.snd f g)} (α : x ⟶ y) :
    (ModuleDerived.pullback (fiberMap f ((CostructuredArrow.map g).map α.base))).obj
        (baseChangeComplex f g y) ≅
      (ModuleDerived.pullback
          (fiberMap f ((CostructuredArrow.map g).map α.base) ≫
            (fiberIso f g y.σ).inv)).obj y.complex :=
  (ModuleDerived.pullbackCompIso (fiberMap f ((CostructuredArrow.map g).map α.base))
      (fiberIso f g y.σ).inv).app y.complex

/-- Transport of the pulled-back complex along the pasting naturality equality. -/
def baseChangeMapIso_path (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : Obj (pullback.snd f g)} (α : x ⟶ y) :
    (ModuleDerived.pullback
        (fiberMap f ((CostructuredArrow.map g).map α.base) ≫ (fiberIso f g y.σ).inv)).obj
      y.complex ≅
      (ModuleDerived.pullback
          ((fiberIso f g x.σ).inv ≫ fiberMap (pullback.snd f g) α.base)).obj y.complex :=
  (ModuleDerived.pullbackCongr (fiberIso_natural_inv f g α.base)).app y.complex

/-- Reassociation of derived pullback along `fiberIso.inv` and the fibre map of `α`. -/
def baseChangeMapIso_reassoc' (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f]
    {x y : Obj (pullback.snd f g)} (α : x ⟶ y) :
    (ModuleDerived.pullback
        ((fiberIso f g x.σ).inv ≫ fiberMap (pullback.snd f g) α.base)).obj y.complex ≅
      (ModuleDerived.pullback (fiberIso f g x.σ).inv).obj
        ((ModuleDerived.pullback (fiberMap (pullback.snd f g) α.base)).obj y.complex) :=
  (ModuleDerived.pullbackCompIso (fiberIso f g x.σ).inv
      (fiberMap (pullback.snd f g) α.base)).symm.app y.complex

/-- The derived isomorphism of `baseChange` on a morphism, transporting `α.iso` along
`fiberIso`. -/
def baseChangeMapIso (f : X ⟶ B) (g : B' ⟶ B) [Proper f] [Flat f] [FinitePresentation f]
    {x y : Obj (pullback.snd f g)} (α : x ⟶ y) :
    (ModuleDerived.pullback (fiberMap f ((CostructuredArrow.map g).map α.base))).obj
        (baseChangeComplex f g y) ≅
      baseChangeComplex f g x :=
  baseChangeMapIso_reassoc f g α ≪≫
    baseChangeMapIso_path f g α ≪≫
    baseChangeMapIso_reassoc' f g α ≪≫
    (ModuleDerived.pullback (fiberIso f g x.σ).inv).mapIso α.iso

/-- The functor `Complexes_{X'/B'} ⥤ Complexes_{X/B}` induced by `g : B' ⟶ B`, with
`X' = X ×_B B'` and `f' = pullback.snd f g`. -/
def baseChange (f : X ⟶ B) (g : B' ⟶ B) [Proper f] [Flat f] [FinitePresentation f] :
    Obj (pullback.snd f g) ⥤ Obj f where
  obj x := baseChangeObj f g x
  map α := homMk ((CostructuredArrow.map g).map α.base) (baseChangeMapIso f g α)
  map_id := sorry
  map_comp := sorry

/-- On objects, `baseChange` sends the test scheme over `B'` to its image under
`CostructuredArrow.map g`. -/
theorem baseChange_obj_σ (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] (x : Obj (pullback.snd f g)) :
    ((baseChange f g).obj x).σ = (CostructuredArrow.map g).obj x.σ :=
  sorry

/-- On objects, `baseChange` transports the complex along `fiberIso.inv`. -/
theorem baseChange_obj_complex (f : X ⟶ B) (g : B' ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f] (x : Obj (pullback.snd f g)) :
    ((baseChange f g).obj x).complex = baseChangeComplex f g x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
