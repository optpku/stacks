/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.Grothendieck
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Bicategory

universe u

namespace AlgebraicGeometry.Scheme

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The pullback pseudofunctor of finite étale categories associated to an inverse system
of schemes. -/
def finiteEtaleDiagram {I : Type u} [Preorder I] (D : OrderDual I ⥤ Scheme.{u}) :
    LocallyDiscrete ((OrderDual I)ᵒᵖ) ⥤ᵖ Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun i ↦ Cat.of (FiniteEtale (D.obj i.unop)))
    (fun arrow ↦ (finiteEtaleBaseChange (D.map arrow.unop)).toCatHom)
    (fun i ↦ Cat.Hom.isoMk (NatIso.ofComponents
      (fun A ↦ MorphismProperty.Over.isoMk
        (pullback.congrHom rfl (D.map_id i.unop) ≪≫
          @asIso _ _ _ _ (pullback.fst A.hom (𝟙 (D.obj i.unop)))
            (@pullback_fst_iso_of_right_iso _ _ _ _ _ A.hom (𝟙 (D.obj i.unop))
              (Iso.refl (D.obj i.unop)).isIso_hom)) (by
        simp [pullback.map, pullback.condition])) (by
      intro A B f
      ext
      simp [pullback.map])))
    (fun arrow next ↦ Cat.Hom.isoMk
      (MorphismProperty.Over.pullbackComp (D.map next.unop) (D.map arrow.unop)
        (D.map (arrow ≫ next).unop) (D.map_comp next.unop arrow.unop)))
    (by
      intro i j k l f g h
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext A
      apply MorphismProperty.Over.Hom.ext
      dsimp [finiteEtaleBaseChange, Functor.toCatHom,
        MorphismProperty.Over.pullback, MorphismProperty.Over.mk]
      apply pullback.hom_ext
      · simp only [pullback.map, Category.comp_id, MorphismProperty.Over.pullbackComp,
          MorphismProperty.Over.pullback, Functor.id_obj, Functor.const_obj_obj,
          MorphismProperty.Over.mk, Functor.comp_obj, NatIso.ofComponents_inv_app,
          MorphismProperty.Over.isoMk_inv_left, Iso.trans_inv, Iso.symm_inv,
          pullback.congrHom_inv, Category.assoc, Category.id_comp, limit.lift_π,
          PullbackCone.mk_pt, PullbackCone.mk_π_app,
          pullbackLeftPullbackSndIso_hom_fst, limit.lift_π_assoc, cospan_left,
          pullbackLeftPullbackSndIso_hom_fst_assoc, pullbackLeftPullbackSndIso_inv_fst]
        rfl
      · simp only [pullback.map, Category.comp_id, MorphismProperty.Over.pullbackComp,
          MorphismProperty.Over.pullback, Functor.id_obj, Functor.const_obj_obj,
          MorphismProperty.Over.mk, Functor.comp_obj, NatIso.ofComponents_inv_app,
          MorphismProperty.Over.isoMk_inv_left, Iso.trans_inv, Iso.symm_inv,
          pullback.congrHom_inv, Category.assoc, Category.id_comp, limit.lift_π,
          PullbackCone.mk_pt, PullbackCone.mk_π_app,
          pullbackLeftPullbackSndIso_hom_snd, pullbackLeftPullbackSndIso_inv_snd_snd]
        rfl)
    (by
      intro i j f
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext A
      apply MorphismProperty.Over.Hom.ext
      dsimp [finiteEtaleBaseChange, Functor.toCatHom,
        MorphismProperty.Over.pullback, MorphismProperty.Over.mk]
      apply pullback.hom_ext
      · simp only [pullback.map, Category.comp_id, limit.lift_π, PullbackCone.mk_pt,
          PullbackCone.mk_π_app, Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
          Category.id_comp]
        rfl
      · simp only [pullback.map, Category.comp_id, limit.lift_π, PullbackCone.mk_pt,
          PullbackCone.mk_π_app, Category.assoc,
          pullbackLeftPullbackSndIso_inv_snd_snd, Category.id_comp]
        rfl)
    (by
      intro i j f
      apply Cat.Hom₂.ext
      apply NatTrans.ext
      funext A
      apply MorphismProperty.Over.Hom.ext
      dsimp [finiteEtaleBaseChange, Functor.toCatHom,
        MorphismProperty.Over.pullback, MorphismProperty.Over.mk]
      apply pullback.hom_ext
      · simp only [pullback.map, Category.comp_id, limit.lift_π, PullbackCone.mk_pt,
          PullbackCone.mk_π_app, Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
          Category.id_comp]
        rfl
      · simp only [pullback.map, Category.comp_id, limit.lift_π, PullbackCone.mk_pt,
          PullbackCone.mk_π_app, Category.assoc, pullback.condition,
          CategoryTheory.Functor.map_id, pullbackLeftPullbackSndIso_inv_snd_snd,
          Category.id_comp]
        rfl)

/-- At each stage, the finite étale diagram is the finite étale category of that scheme. -/
theorem finiteEtaleDiagram_obj {I : Type u} [Preorder I] (D : OrderDual I ⥤ Scheme.{u})
    (i : (OrderDual I)ᵒᵖ) :
    (finiteEtaleDiagram D).obj ⟨i⟩ = Cat.of (FiniteEtale (D.obj i.unop)) :=
  rfl

/-- Transition maps of the finite étale diagram are base change along the inverse system. -/
theorem finiteEtaleDiagram_map {I : Type u} [Preorder I] (D : OrderDual I ⥤ Scheme.{u})
    {i j : (OrderDual I)ᵒᵖ} (arrow : i ⟶ j) :
    (finiteEtaleDiagram D).map arrow.toLoc =
      (finiteEtaleBaseChange (D.map arrow.unop)).toCatHom :=
  rfl

/-- The Grothendieck category of stagewise finite étale schemes and base-change morphisms. -/
abbrev FiniteEtaleTotal {I : Type u} [Preorder I] (D : OrderDual I ⥤ Scheme.{u}) :=
  Pseudofunctor.Grothendieck (finiteEtaleDiagram D)

/-- Transition morphisms in the finite étale Grothendieck category have isomorphic
fiber components. -/
def finiteEtaleTransition {I : Type u} [Preorder I] (D : OrderDual I ⥤ Scheme.{u}) :
    MorphismProperty (FiniteEtaleTotal D) :=
  fun _ _ arrow ↦ IsIso arrow.fiber

/-- The categorical colimit of finite étale categories is modeled by localization at
transition morphisms with isomorphic fiber components. -/
abbrev FiniteEtaleColimit {I : Type u} [Preorder I] (D : OrderDual I ⥤ Scheme.{u}) :=
  (finiteEtaleTransition D).Localization

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pullback along cone legs sends the finite étale Grothendieck category to finite étale
schemes over the cone point. -/
def finiteEtaleTotalComparison {I : Type u} [Preorder I] {D : OrderDual I ⥤ Scheme.{u}}
    (c : Cone D) : FiniteEtaleTotal D ⥤ FiniteEtale c.pt where
  obj A := (finiteEtaleBaseChange (c.π.app A.base.unop)).obj A.fiber
  map {A B} arrow :=
    (MorphismProperty.Over.pullbackComp (c.π.app B.base.unop) (D.map arrow.base.unop)
      (c.π.app A.base.unop) (c.w arrow.base.unop).symm).hom.app A.fiber ≫
      (finiteEtaleBaseChange (c.π.app B.base.unop)).map arrow.fiber
  map_id := by
    intro A
    ext
    dsimp [finiteEtaleDiagram, LocallyDiscrete.mkPseudofunctor,
      pseudofunctorOfIsLocallyDiscrete, finiteEtaleBaseChange, Functor.toCatHom,
      MorphismProperty.Over.pullback, MorphismProperty.Over.mk]
    apply pullback.hom_ext
    · simp [MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, pullback.map, Category.assoc, Category.id_comp,
        Category.comp_id]
    · simp [MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, pullback.map, Category.assoc, Category.id_comp,
        Category.comp_id]
  map_comp := by
    intro A B C f g
    ext
    dsimp [Pseudofunctor.Grothendieck.categoryStruct_comp_fiber, finiteEtaleDiagram,
      LocallyDiscrete.mkPseudofunctor, pseudofunctorOfIsLocallyDiscrete, finiteEtaleBaseChange, Functor.toCatHom,
      MorphismProperty.Over.pullback, MorphismProperty.Over.mk]
    apply pullback.hom_ext
    · simp only [MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullback,
        Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.mk,
        Functor.comp_obj, pullback.map, Category.comp_id, Category.assoc, limit.lift_π,
        PullbackCone.mk_pt, PullbackCone.mk_π_app]
      simp only [← Category.assoc]
      apply congrArg (fun k => k ≫ g.fiber.left)
      apply pullback.hom_ext
      · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          pullbackLeftPullbackSndIso_inv_fst]
        simp only [← Category.assoc]
        apply congrArg (fun k => k ≫ f.fiber.left)
        apply pullback.hom_ext
        · simp [Category.assoc]
        · simp [Category.assoc, pullback.condition, c.w]
      · simp [Category.assoc, pullback.condition]
    · simp [MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, pullback.map, Category.assoc, Category.comp_id]

/-- Cone-leg pullback inverts finite étale transition morphisms with isomorphic fiber
components. -/
theorem finiteEtaleTotalComparison_inverts {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Scheme.{u}} (c : Cone D) :
    (finiteEtaleTransition D).IsInvertedBy (finiteEtaleTotalComparison c) :=
  fun A B arrow h ↦ IsIso.comp_isIso'
    ((MorphismProperty.Over.pullbackComp (c.π.app B.base.unop) (D.map arrow.base.unop)
      (c.π.app A.base.unop) (c.w arrow.base.unop).symm).app A.fiber).isIso_hom
    (@Functor.map_isIso _ _ _ _ _ _
      (finiteEtaleBaseChange (c.π.app B.base.unop)) arrow.fiber h)

/-- The canonical comparison from the colimit of stagewise finite étale categories to the
finite étale category of the limit scheme. -/
def finiteEtaleColimitComparison {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) :
    FiniteEtaleColimit D ⥤ FiniteEtale c.pt :=
  Localization.Construction.lift (finiteEtaleTotalComparison c)
    (finiteEtaleTotalComparison_inverts c)

/-- The localization comparison sends a stage object to its pullback along the cone leg. -/
theorem finiteEtaleColimitComparison_obj {I : Type u} [Preorder I]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (A : FiniteEtaleTotal D) :
    (finiteEtaleColimitComparison D c).obj ((finiteEtaleTransition D).Q.obj A) =
      (finiteEtaleBaseChange (c.π.app A.base.unop)).obj A.fiber :=
  rfl

/-- For a directed inverse system of quasi-compact, quasi-separated schemes with affine
transitions, the canonical finite étale comparison at the limit is an equivalence. -/
theorem finiteEtale_colimit_equivalence
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j).carrier]
    [∀ j, QuasiSeparatedSpace (D.obj j).carrier]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))] :
    (finiteEtaleColimitComparison D c).IsEquivalence := sorry

end AlgebraicGeometry.Scheme
