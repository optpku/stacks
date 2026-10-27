/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute

-- Import decisions:
-- * `Map` owns the square induced by a morphism into the canonical two-fibre product.
-- * `Target` owns the square induced directly by a pseudo-pullback cone.
--   The comparison here only assembles their two leg isomorphisms.
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Comparison.Map
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Comparison.Target

/-!
# Comparison isomorphism for relative representability

This leaf assembles the two explicit leg comparisons into the canonical natural isomorphism from
the map induced by a cone morphism to the ordinary categorical-pullback target of that cone.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback
open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids.PseudoPullbackComparison

section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- The left-leg isomorphism comparing the map induced by u with the target attached to P. -/
@[stacks 0H2E "left leg of the pseudo-pullback comparison"]
noncomputable def fstIso
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection) :
    (map.square (PseudoPullbackCone.map u)).fst ≅
      (target.square P).fst :=
  map.square.fstIso (PseudoPullbackCone.map u) ≪≫
    FiberedCategoryOver.Groupoids.toFunctorIso (PseudoPullbackCone.fstIso u) ≪≫
      (target.square.fstIso P).symm

/-- The right-leg isomorphism comparing the map induced by u with the target attached to P. -/
@[stacks 0H2E "right leg of the pseudo-pullback comparison"]
noncomputable def sndIso
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection) :
    (map.square (PseudoPullbackCone.map u)).snd ≅
      (target.square P).snd :=
  map.square.sndIso (PseudoPullbackCone.map u) ≪≫
    FiberedCategoryOver.Groupoids.toFunctorIso (PseudoPullbackCone.sndIso u) ≪≫
      (target.square.sndIso P).symm

namespace fstIso

/-- The forward component of the left-leg comparison is the composite of the map-square,
cone-morphism, and target-square comparison components. -/
@[simp]
theorem hom.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    (fstIso u).hom.app a =
      (map.square.fstIso (PseudoPullbackCone.map u)).hom.app a ≫
        (FiberedCategoryOver.Groupoids.toFunctorIso
          (PseudoPullbackCone.fstIso u)).hom.app a ≫
          (target.square.fstIso P).inv.app a := by
  rfl

/-- The inverse component of the left-leg comparison is the reverse composite of the
target-square, cone-morphism, and map-square comparison components. -/
@[simp]
theorem inv.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    (fstIso u).inv.app a =
      (target.square.fstIso P).hom.app a ≫
        (FiberedCategoryOver.Groupoids.toFunctorIso
          (PseudoPullbackCone.fstIso u)).inv.app a ≫
          (map.square.fstIso (PseudoPullbackCone.map u)).inv.app a := by
  simp only [fstIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc]
  rfl

end fstIso

namespace sndIso

/-- The forward component of the right-leg comparison is the composite of the map-square,
cone-morphism, and target-square comparison components. -/
@[simp]
theorem hom.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    (sndIso u).hom.app a =
      (map.square.sndIso (PseudoPullbackCone.map u)).hom.app a ≫
        (FiberedCategoryOver.Groupoids.toFunctorIso
          (PseudoPullbackCone.sndIso u)).hom.app a ≫
          (target.square.sndIso P).inv.app a := by
  rfl

/-- The inverse component of the right-leg comparison is the reverse composite of the
target-square, cone-morphism, and map-square comparison components. -/
@[simp]
theorem inv.app
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    (sndIso u).inv.app a =
      (target.square.sndIso P).hom.app a ≫
        (FiberedCategoryOver.Groupoids.toFunctorIso
          (PseudoPullbackCone.sndIso u)).inv.app a ≫
          (map.square.sndIso (PseudoPullbackCone.map u)).inv.app a := by
  simp only [sndIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Category.assoc]
  rfl

end sndIso

namespace Implementation

set_option backward.isDefEq.respectTransparency false in
/-- The transported leg isomorphisms satisfy the coherence required by
CategoricalPullback.mkNatIso.

The two leg cells and both structural comparisons lie over the identity of the source base.
Their images in C are therefore equality transports, whose composites agree. -/
private theorem legsCompatible
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection) :
    Functor.whiskerRight (fstIso u).hom X.p ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (target P)
            (CatCommSq.iso (π₁ X.p X.p) (π₂ X.p X.p) X.p X.p).hom ≫
          (Functor.associator _ _ _).inv =
      (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (map (PseudoPullbackCone.map u))
            (CatCommSq.iso (π₁ X.p X.p) (π₂ X.p X.p) X.p X.p).hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight (sndIso u).hom X.p := by
  apply NatTrans.ext
  funext a
  change X.p.map ((fstIso u).hom.app a) ≫
      𝟙 _ ≫ ((target P).obj a).iso.hom ≫ 𝟙 _ =
    𝟙 _ ≫ ((map (PseudoPullbackCone.map u)).obj a).iso.hom ≫
      𝟙 _ ≫ X.p.map ((sndIso u).hom.app a)
  simp only [Category.id_comp, Category.comp_id]
  let M := PseudoPullbackCone.map u
  let F := FiberedCategoryOver.Groupoids.toBasedFunctor X.baseProjection
  have hf := IsHomLift.fac' X.p (𝟙 (P.pt.p.obj a))
    ((PseudoPullbackCone.fstFac u).hom.toNatTrans.app a)
  have hs := IsHomLift.fac' X.p (𝟙 (P.pt.p.obj a))
    ((PseudoPullbackCone.sndFac u).hom.toNatTrans.app a)
  have ht := IsHomLift.fac' (FiberedCategoryOver.Groupoids.base.{u, v, w} C).p
    (𝟙 (P.pt.p.obj a)) (P.iso.hom.hom.toNatTrans.app a)
  have hm' : Functor.IsHomLift (FiberedCategoryOver.Groupoids.base.{u, v, w} C).p
      (𝟙 (P.pt.p.obj a)) (map.comparisonObj M a).iso.hom := by
    exact (BasedCategory.PseudoPullback.comparisonIso F F).hom.isHomLift
      ((FiberedCategoryOver.Groupoids.toBasedFunctor M).w_obj a)
  have hm := IsHomLift.fac' (FiberedCategoryOver.Groupoids.base.{u, v, w} C).p
    (𝟙 (P.pt.p.obj a)) (map.comparisonObj M a).iso.hom
  have hf0 : (fstIso u).hom.app a =
      (PseudoPullbackCone.fstFac u).hom.toNatTrans.app a := by
    change 𝟙 _ ≫ _ ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
    rfl
  have hs0 : (sndIso u).hom.app a =
      (PseudoPullbackCone.sndFac u).hom.toNatTrans.app a := by
    change 𝟙 _ ≫ _ ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
    rfl
  rw [hf0, hs0, target.obj.iso.hom.{w, v, u, w, w}, map.obj.iso.hom.{w, v, u, w, w}]
  simp only [FiberedCategoryOver.Groupoids.baseProjection.iso.inv.app.{u, v, w, w},
    FiberedCategoryOver.Groupoids.baseProjection.iso.hom.app.{u, v, w, w},
    FiberedCategoryOver.Groupoids.baseSection.projection.appIso,
    Iso.refl_hom, Iso.refl_inv, Category.id_comp]
  rw [FiberedCategoryOver.Groupoids.toFunctorIso.hom.app]
  rw [hf, hs, ht, hm]
  simp only [InducedBicategory.categoryStruct_comp_hom, BasedCategory.comp_def,
    Category.id_comp, eqToHom_trans, eqToHom_trans_assoc, Category.assoc]
  erw [Category.comp_id, Category.id_comp]
  simp

end Implementation

/-- The canonical comparison isomorphism from the map induced by u to the ordinary
categorical-pullback functor attached to P. Both sides land in X.p ⊡ X.p; the implementation
ULift is confined to BaseProjection.pullbackDown. -/
@[stacks 0H2E "comparison from a pseudo-pullback cone to its categorical pullback"]
noncomputable def iso
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection) :
    map (PseudoPullbackCone.map u) ≅
      target P :=
  CategoricalPullback.mkNatIso
    (fstIso u)
    (sndIso u)
    (coh := Implementation.legsCompatible u)

/-- The first component of the forward comparison is the forward left-leg comparison. -/
@[simp]
theorem iso.hom.app.fst
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    ((iso u).hom.app a).fst = (fstIso u).hom.app a := by
  rfl

/-- The second component of the forward comparison is the forward right-leg comparison. -/
@[simp]
theorem iso.hom.app.snd
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    ((iso u).hom.app a).snd = (sndIso u).hom.app a := by
  rfl

/-- The first component of the inverse comparison is the inverse left-leg comparison. -/
@[simp]
theorem iso.inv.app.fst
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    ((iso u).inv.app a).fst = (fstIso u).inv.app a := by
  rfl

/-- The second component of the inverse comparison is the inverse right-leg comparison. -/
@[simp]
theorem iso.inv.app.snd
    {X : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
    {P : Bicategory.PseudoPullbackCone X.baseProjection X.baseProjection}
    (u : P ⟶
      CategoryTheory.TwoFibreProduct.cone X.baseProjection X.baseProjection)
    (a : P.pt.total) :
    ((iso u).inv.app a).snd = (sndIso u).inv.app a := by
  rfl

end

end FiberedCategoryOver.Groupoids.PseudoPullbackComparison

end CategoryTheory
