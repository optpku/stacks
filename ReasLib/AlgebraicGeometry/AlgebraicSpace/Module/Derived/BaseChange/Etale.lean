/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LowerShriek
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ExtensionComparison
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel

/-! # Étale base change from chart limits and K-injective complexes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ComplexShape
open CategoryTheory.Sheaf.InternalModule RingedSite.ToposHom

noncomputable section

set_option backward.isDefEq.respectTransparency false
-- Public comparisons retain their private chart and cochain implementations.
set_option backward.privateInPublic true

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.EtaleBaseChangeModel

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
variable {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable [Etale g] [Etale h]

private abbrev chartIndex (f : X ⟶ Y) (V : smallEtaleSite Y) :=
  StructuredArrow (op ((etaleBaseChange f).obj V)) (smallEtaleToSpaces X).op

private def chartLift (sq : IsPullback h f' f g) (V : smallEtaleSite Y')
    (a : chartIndex f ((restrictPostcompose g).obj V)) :
    ofOver a.right.unop.left ⟶ X' :=
  sq.lift a.right.unop.hom
    (a.hom.unop.left ≫ etaleBaseChangeSnd f ((restrictPostcompose g).obj V) ≫ V.hom)
    (by
      have aw : a.hom.unop.left ≫
          etaleBaseChangeHom f ((restrictPostcompose g).obj V) = a.right.unop.hom := by
        exact MorphismProperty.Over.w a.hom.unop
      rw [← aw, Category.assoc]
      exact (congrArg (fun m ↦ a.hom.unop.left ≫ m)
        (pullback.condition (f := homFunctor f)
          (g := homFunctor ((restrictPostcompose g).obj V).hom))).trans
            (by simp only [Category.assoc]; rfl))

private theorem liftedChart_etale (sq : IsPullback h f' f g) (V : smallEtaleSite Y')
    (a : chartIndex f ((restrictPostcompose g).obj V)) :
    Etale (chartLift sq V a) := sorry

private def liftedChart (sq : IsPullback h f' f g) (V : smallEtaleSite Y')
    (a : chartIndex f ((restrictPostcompose g).obj V)) : smallEtaleSite X' :=
  smallEtaleSite.mk (chartLift sq V a) (liftedChart_etale sq V a)

private def liftedArrow (sq : IsPullback h f' f g) (V : smallEtaleSite Y')
    (a : chartIndex f ((restrictPostcompose g).obj V)) : chartIndex f' V :=
  StructuredArrow.mk (Y := op (liftedChart sq V a))
    (show (smallEtaleToSpaces X').obj (liftedChart sq V a) ⟶ (etaleBaseChange f').obj V from
      MorphismProperty.Over.homMk
      (pullback.lift (f := homFunctor f') (g := homFunctor V.hom)
        (chartLift sq V a)
        (a.hom.unop.left ≫ etaleBaseChangeSnd f ((restrictPostcompose g).obj V))
        (by exact sq.lift_snd _ _ _))
      (by exact pullback.lift_fst (f := homFunctor f') (g := homFunctor V.hom) _ _ _)).op

private def cartesianChartMap (sq : IsPullback h f' f g) (V : smallEtaleSite Y') :
    etaleBaseChangeSpace f' V ⟶
      etaleBaseChangeSpace f ((restrictPostcompose g).obj V) :=
  pullback.lift (f := homFunctor f) (g := homFunctor ((restrictPostcompose g).obj V).hom)
    (etaleBaseChangeHom f' V ≫ h) (etaleBaseChangeSnd f' V)
    (by
      change (etaleBaseChangeHom f' V ≫ h) ≫ f =
        etaleBaseChangeSnd f' V ≫ (V.hom ≫ g)
      rw [Category.assoc, sq.w, ← Category.assoc]
      exact (congrArg (fun m ↦ m ≫ g)
        (pullback.condition (f := homFunctor f') (g := homFunctor V.hom))).trans
          (Category.assoc _ _ _))

private def postcomposedArrow (sq : IsPullback h f' f g) (V : smallEtaleSite Y')
    (a : chartIndex f' V) : chartIndex f ((restrictPostcompose g).obj V) :=
  StructuredArrow.mk
    (Y := op ((restrictPostcompose h).obj a.right.unop))
    (show (smallEtaleToSpaces X).obj ((restrictPostcompose h).obj a.right.unop) ⟶
        (etaleBaseChange f).obj ((restrictPostcompose g).obj V) from
      MorphismProperty.Over.homMk
      (a.hom.unop.left ≫ cartesianChartMap sq V)
      (by
        change (a.hom.unop.left ≫ cartesianChartMap sq V) ≫
          etaleBaseChangeHom f ((restrictPostcompose g).obj V) = a.right.unop.hom ≫ h
        have p : cartesianChartMap sq V ≫
            etaleBaseChangeHom f ((restrictPostcompose g).obj V) =
              etaleBaseChangeHom f' V ≫ h :=
          pullback.lift_fst (f := homFunctor f)
            (g := homFunctor ((restrictPostcompose g).obj V).hom) _ _ _
        exact (Category.assoc _ _ _).trans
          ((congrArg (fun m ↦ a.hom.unop.left ≫ m) p).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (fun m ↦ m ≫ h) (MorphismProperty.Over.w a.hom.unop)))))).op


private def chartForward (sq : IsPullback h f' f g) (V : smallEtaleSite Y') :
    chartIndex f ((restrictPostcompose g).obj V) ⥤ chartIndex f' V where
  obj := liftedArrow sq V
  map {a b} k :=
    StructuredArrow.homMk
      (show liftedChart sq V b ⟶ liftedChart sq V a from
        MorphismProperty.CostructuredArrow.homMk k.right.unop.left trivial (by
        change ofOverMap k.right.unop.left ≫ chartLift sq V a = chartLift sq V b
        apply sq.hom_ext
        · simp only [chartLift, Category.assoc, sq.lift_fst]
          exact (smallEtaleSite.w k.right.unop)
        · simp only [chartLift, Category.assoc, sq.lift_snd]
          have w : ofOverMap k.right.unop.left ≫ a.hom.unop.left = b.hom.unop.left :=
            congrArg (fun m ↦ m.unop.left) (StructuredArrow.w k)
          simpa only [Category.assoc] using
            congrArg (fun m ↦ m ≫ etaleBaseChangeSnd f ((restrictPostcompose g).obj V) ≫ V.hom) w)).op
      (by
        apply Quiver.Hom.unop_inj
        apply MorphismProperty.Over.Hom.ext
        change ofOverMap k.right.unop.left ≫
          (liftedArrow sq V a).hom.unop.left = (liftedArrow sq V b).hom.unop.left
        apply pullback.hom_ext (f := homFunctor f') (g := homFunctor V.hom)
        · have pa : (liftedArrow sq V a).hom.unop.left ≫
              etaleBaseChangeHom f' V = chartLift sq V a :=
            MorphismProperty.Over.w (liftedArrow sq V a).hom.unop
          have pb : (liftedArrow sq V b).hom.unop.left ≫
              etaleBaseChangeHom f' V = chartLift sq V b :=
            MorphismProperty.Over.w (liftedArrow sq V b).hom.unop
          change (ofOverMap k.right.unop.left ≫ (liftedArrow sq V a).hom.unop.left) ≫
            etaleBaseChangeHom f' V = (liftedArrow sq V b).hom.unop.left ≫
              etaleBaseChangeHom f' V
          rw [Category.assoc, pa, pb]
          apply sq.hom_ext
          · simp only [chartLift, Category.assoc, sq.lift_fst]
            exact smallEtaleSite.w k.right.unop
          · simp only [chartLift, Category.assoc, sq.lift_snd]
            have w : ofOverMap k.right.unop.left ≫ a.hom.unop.left = b.hom.unop.left :=
              congrArg (fun m ↦ m.unop.left) (StructuredArrow.w k)
            simpa only [Category.assoc] using congrArg
              (fun m ↦ m ≫ etaleBaseChangeSnd f ((restrictPostcompose g).obj V) ≫ V.hom) w
        · have pa : (liftedArrow sq V a).hom.unop.left ≫ etaleBaseChangeSnd f' V =
              a.hom.unop.left ≫ etaleBaseChangeSnd f ((restrictPostcompose g).obj V) :=
            pullback.lift_snd (f := homFunctor f') (g := homFunctor V.hom) _ _ _
          have pb : (liftedArrow sq V b).hom.unop.left ≫ etaleBaseChangeSnd f' V =
              b.hom.unop.left ≫ etaleBaseChangeSnd f ((restrictPostcompose g).obj V) :=
            pullback.lift_snd (f := homFunctor f') (g := homFunctor V.hom) _ _ _
          change (ofOverMap k.right.unop.left ≫ (liftedArrow sq V a).hom.unop.left) ≫
            etaleBaseChangeSnd f' V = (liftedArrow sq V b).hom.unop.left ≫
              etaleBaseChangeSnd f' V
          rw [Category.assoc, pa, pb]
          have w : ofOverMap k.right.unop.left ≫ a.hom.unop.left = b.hom.unop.left :=
            congrArg (fun m ↦ m.unop.left) (StructuredArrow.w k)
          simpa only [Category.assoc] using
            congrArg (fun m ↦ m ≫ etaleBaseChangeSnd f ((restrictPostcompose g).obj V)) w)
  map_id _ := by
    apply StructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    exact MorphismProperty.CostructuredArrow.Hom.ext rfl
  map_comp _ _ := by
    apply StructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    exact MorphismProperty.CostructuredArrow.Hom.ext rfl

private def chartBackward (sq : IsPullback h f' f g) (V : smallEtaleSite Y') :
    chartIndex f' V ⥤ chartIndex f ((restrictPostcompose g).obj V) where
  obj := postcomposedArrow sq V
  map {a b} k :=
    StructuredArrow.homMk ((restrictPostcompose h).map k.right.unop).op (by
      apply Quiver.Hom.unop_inj
      apply MorphismProperty.Over.Hom.ext
      have w : ofOverMap k.right.unop.left ≫ a.hom.unop.left = b.hom.unop.left :=
        congrArg (fun m ↦ m.unop.left) (StructuredArrow.w k)
      change ofOverMap k.right.unop.left ≫
        (a.hom.unop.left ≫ cartesianChartMap sq V) = b.hom.unop.left ≫ cartesianChartMap sq V
      simpa only [Category.assoc] using
        congrArg (fun m ↦ m ≫ cartesianChartMap sq V) w)
  map_id _ := by
    apply StructuredArrow.hom_ext
    exact congrArg Quiver.Hom.op ((restrictPostcompose h).map_id _)
  map_comp _ _ := by
    apply StructuredArrow.hom_ext
    exact congrArg Quiver.Hom.op ((restrictPostcompose h).map_comp _ _)

private def chartSectionComparison (sq : IsPullback h f' f g) (V : smallEtaleSite Y')
    (a : chartIndex f ((restrictPostcompose g).obj V)) :
    (restrictPostcompose h).obj (liftedChart sq V a) ≅ a.right.unop where
  hom := MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial (by
    change 𝟙 _ ≫ a.right.unop.hom = chartLift sq V a ≫ h
    rw [Category.id_comp]
    exact (sq.lift_fst _ _ _).symm)
  inv := MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial (by
    change 𝟙 _ ≫ (chartLift sq V a ≫ h) = a.right.unop.hom
    rw [Category.id_comp]
    exact sq.lift_fst _ _ _)
  hom_inv_id := MorphismProperty.CostructuredArrow.Hom.ext (Category.id_comp _)
  inv_hom_id := MorphismProperty.CostructuredArrow.Hom.ext (Category.id_comp _)

private theorem liftedArrow_cartesianChartMap (sq : IsPullback h f' f g)
    (V : smallEtaleSite Y') (a : chartIndex f ((restrictPostcompose g).obj V)) :
    (liftedArrow sq V a).hom.unop.left ≫ cartesianChartMap sq V = a.hom.unop.left := by
  apply pullback.hom_ext (f := homFunctor f)
    (g := homFunctor ((restrictPostcompose g).obj V).hom)
  · change (_ ≫ cartesianChartMap sq V) ≫ etaleBaseChangeHom f _ = _
    have p : cartesianChartMap sq V ≫ etaleBaseChangeHom f _ =
        etaleBaseChangeHom f' V ≫ h :=
      pullback.lift_fst (f := homFunctor f)
        (g := homFunctor ((restrictPostcompose g).obj V).hom) _ _ _
    rw [Category.assoc, p, ← Category.assoc]
    have pa : (liftedArrow sq V a).hom.unop.left ≫ etaleBaseChangeHom f' V =
        chartLift sq V a := MorphismProperty.Over.w (liftedArrow sq V a).hom.unop
    exact (congrArg (fun m ↦ m ≫ h) pa).trans
      ((sq.lift_fst _ _ _).trans (MorphismProperty.Over.w a.hom.unop).symm)
  · change (_ ≫ cartesianChartMap sq V) ≫ etaleBaseChangeSnd f _ = _
    have p : cartesianChartMap sq V ≫ etaleBaseChangeSnd f _ = etaleBaseChangeSnd f' V :=
      pullback.lift_snd (f := homFunctor f)
        (g := homFunctor ((restrictPostcompose g).obj V).hom) _ _ _
    rw [Category.assoc, p]
    exact pullback.lift_snd (f := homFunctor f') (g := homFunctor V.hom) _ _ _

private def chartUnit (sq : IsPullback h f' f g) (V : smallEtaleSite Y')
    (a : chartIndex f ((restrictPostcompose g).obj V)) :
    a ≅ (chartBackward sq V).obj ((chartForward sq V).obj a) :=
  StructuredArrow.isoMk (chartSectionComparison sq V a).op (by
    apply Quiver.Hom.unop_inj
    apply MorphismProperty.Over.Hom.ext
    change ofOverMap (𝟙 a.right.unop.left) ≫ a.hom.unop.left =
      (liftedArrow sq V a).hom.unop.left ≫ cartesianChartMap sq V
    exact (congrArg (fun m : ofOver a.right.unop.left ⟶ ofOver a.right.unop.left ↦
      m ≫ a.hom.unop.left) (yoneda.map_id a.right.unop.left)).trans
        ((Category.id_comp _).trans (liftedArrow_cartesianChartMap sq V a).symm))

private theorem chartLift_postcomposed (sq : IsPullback h f' f g)
    (V : smallEtaleSite Y') (a : chartIndex f' V) :
    chartLift sq V (postcomposedArrow sq V a) = a.right.unop.hom := by
  apply sq.hom_ext
  · exact sq.lift_fst _ _ _
  · have p : cartesianChartMap sq V ≫ etaleBaseChangeSnd f _ = etaleBaseChangeSnd f' V :=
      pullback.lift_snd (f := homFunctor f)
        (g := homFunctor ((restrictPostcompose g).obj V).hom) _ _ _
    change chartLift sq V (postcomposedArrow sq V a) ≫ f' = a.right.unop.hom ≫ f'
    rw [show chartLift sq V (postcomposedArrow sq V a) ≫ f' =
        (a.hom.unop.left ≫ cartesianChartMap sq V) ≫ etaleBaseChangeSnd f _ ≫ V.hom from
          sq.lift_snd _ _ _]
    calc
      (a.hom.unop.left ≫ cartesianChartMap sq V) ≫ etaleBaseChangeSnd f _ ≫ V.hom =
          a.hom.unop.left ≫ (cartesianChartMap sq V ≫ etaleBaseChangeSnd f _) ≫ V.hom :=
        by simp only [Category.assoc]
      _ = a.hom.unop.left ≫ etaleBaseChangeSnd f' V ≫ V.hom :=
        congrArg (fun m ↦ a.hom.unop.left ≫ m ≫ V.hom) p
      _ = (a.hom.unop.left ≫ etaleBaseChangeHom f' V) ≫ f' :=
        (congrArg (fun m ↦ a.hom.unop.left ≫ m)
          (pullback.condition (f := homFunctor f') (g := homFunctor V.hom)).symm).trans
            (Category.assoc _ _ _).symm
      _ = a.right.unop.hom ≫ f' :=
        congrArg (fun m ↦ m ≫ f') (MorphismProperty.Over.w a.hom.unop)

private def chartCounit (sq : IsPullback h f' f g) (V : smallEtaleSite Y')
    (a : chartIndex f' V) :
    (chartForward sq V).obj ((chartBackward sq V).obj a) ≅ a :=
  StructuredArrow.isoMk
    (show liftedChart sq V (postcomposedArrow sq V a) ≅ a.right.unop from
      { hom := MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial (by
          change ofOverMap (𝟙 _) ≫ a.right.unop.hom = chartLift sq V (postcomposedArrow sq V a)
          exact (congrArg (fun m : ofOver a.right.unop.left ⟶ ofOver a.right.unop.left ↦
            m ≫ a.right.unop.hom) (yoneda.map_id a.right.unop.left)).trans
              ((Category.id_comp _).trans (chartLift_postcomposed sq V a).symm))
        inv := MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial (by
          change ofOverMap (𝟙 _) ≫ chartLift sq V (postcomposedArrow sq V a) = a.right.unop.hom
          exact (congrArg (fun m : ofOver a.right.unop.left ⟶ ofOver a.right.unop.left ↦
            m ≫ chartLift sq V (postcomposedArrow sq V a)) (yoneda.map_id a.right.unop.left)).trans
              ((Category.id_comp _).trans (chartLift_postcomposed sq V a)))
        hom_inv_id := MorphismProperty.CostructuredArrow.Hom.ext (Category.id_comp _)
        inv_hom_id := MorphismProperty.CostructuredArrow.Hom.ext (Category.id_comp _) }).symm.op
    (by
      apply Quiver.Hom.unop_inj
      apply MorphismProperty.Over.Hom.ext
      change ofOverMap (𝟙 _) ≫ (liftedArrow sq V (postcomposedArrow sq V a)).hom.unop.left =
        a.hom.unop.left
      apply ((congrArg (fun m : ofOver a.right.unop.left ⟶ ofOver a.right.unop.left ↦
        m ≫ (liftedArrow sq V (postcomposedArrow sq V a)).hom.unop.left)
          (yoneda.map_id a.right.unop.left)).trans (Category.id_comp _)).trans
      apply pullback.hom_ext (f := homFunctor f') (g := homFunctor V.hom)
      · change _ ≫ etaleBaseChangeHom f' V = _
        exact (MorphismProperty.Over.w
          (liftedArrow sq V (postcomposedArrow sq V a)).hom.unop).trans
            ((chartLift_postcomposed sq V a).trans (MorphismProperty.Over.w a.hom.unop).symm)
      · have p : cartesianChartMap sq V ≫ etaleBaseChangeSnd f _ = etaleBaseChangeSnd f' V :=
          pullback.lift_snd (f := homFunctor f)
            (g := homFunctor ((restrictPostcompose g).obj V).hom) _ _ _
        change _ ≫ etaleBaseChangeSnd f' V = _
        exact (pullback.lift_snd (f := homFunctor f') (g := homFunctor V.hom) _ _ _).trans
          ((Category.assoc _ _ _).trans (congrArg (fun m ↦ a.hom.unop.left ≫ m) p)))

private def chartEquivalence (sq : IsPullback h f' f g) (V : smallEtaleSite Y') :
    chartIndex f ((restrictPostcompose g).obj V) ≌ chartIndex f' V :=
  CategoryTheory.Equivalence.mk (chartForward sq V) (chartBackward sq V)
    (NatIso.ofComponents (chartUnit sq V) (by
      intro a b k
      apply StructuredArrow.hom_ext
      apply Quiver.Hom.unop_inj
      apply MorphismProperty.CostructuredArrow.Hom.ext
      change 𝟙 _ ≫ k.right.unop.left = k.right.unop.left ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]))
    (NatIso.ofComponents (chartCounit sq V) (by
      intro a b k
      apply StructuredArrow.hom_ext
      apply Quiver.Hom.unop_inj
      apply MorphismProperty.CostructuredArrow.Hom.ext
      change 𝟙 _ ≫ k.right.unop.left = k.right.unop.left ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]))

private def chartDiagramIso (sq : IsPullback h f' f g) (F : X.Modules)
    (V : smallEtaleSite Y') :
    (chartEquivalence sq V).functor ⋙
        StructuredArrow.proj (op ((etaleBaseChange f').obj V)) (smallEtaleToSpaces X').op ⋙
          ((ToInternal.underlying (structureSheaf X')).obj ((restrictFunctor h).obj F)).obj ≅
      StructuredArrow.proj (op ((etaleBaseChange f).obj ((restrictPostcompose g).obj V)))
        (smallEtaleToSpaces X).op ⋙ ((ToInternal.underlying (structureSheaf X)).obj F).obj :=
  NatIso.ofComponents
    (fun a ↦
      ((sheafToPresheaf _ (Type u)).mapIso ((restrictUnderlyingIsoPostcompose h).app F)).app
          (op (liftedChart sq V a)) ≪≫
        ((ToInternal.underlying (structureSheaf X)).obj F).obj.mapIso
          (chartSectionComparison sq V a).symm.op)
    (by
      intro a b k
      change _ ≫ _ = _ ≫ _
      dsimp
      change ((ToInternal.underlying (structureSheaf X)).obj F).obj.map
          (((restrictPostcompose h).map ((chartForward sq V).map k).right.unop).op) ≫
          ((ToInternal.underlying (structureSheaf X)).obj F).obj.map
            (chartSectionComparison sq V b).inv.op =
        ((ToInternal.underlying (structureSheaf X)).obj F).obj.map
            (chartSectionComparison sq V a).inv.op ≫
          ((ToInternal.underlying (structureSheaf X)).obj F).obj.map k.right
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      congr 1)

private def sectionCone (sq : IsPullback h f' f g) (F : X.Modules)
    (V : smallEtaleSite Y') :
    Cone (StructuredArrow.proj
      (op ((etaleBaseChange f).obj ((restrictPostcompose g).obj V)))
      (smallEtaleToSpaces X).op ⋙ ((ToInternal.underlying (structureSheaf X)).obj F).obj) :=
  (Cones.postcompose (chartDiagramIso sq F V).hom).obj
    ((EtaleTopos.allChartCone X'
      ((ToInternal.underlying (structureSheaf X')).obj ((restrictFunctor h).obj F))
      ((etaleBaseChange f').obj V)).whisker (chartEquivalence sq V).functor)

private def sectionInv (sq : IsPullback h f' f g) (F : X.Modules)
    (V : (smallEtaleSite Y')ᵒᵖ) :
    ((ToInternal.underlying (structureSheaf Y')).obj
        ((pushforward f').obj ((restrictFunctor h).obj F))).obj.obj V ⟶
      ((ToInternal.underlying (structureSheaf Y')).obj
        ((restrictFunctor g).obj ((pushforward f).obj F))).obj.obj V :=
  ((ModulePushforward.forgetIso (ringedToposHom f')).hom.app
      ((restrictFunctor h).obj F)).hom.app V ≫
    (EtaleTopos.allChartIsLimit X ((ToInternal.underlying (structureSheaf X)).obj F)
      ((etaleBaseChange f).obj ((restrictPostcompose g).obj V.unop))).lift
        (sectionCone sq F V.unop) ≫
    ((ModulePushforward.forgetIso (ringedToposHom f)).inv.app F).hom.app
      (op ((restrictPostcompose g).obj V.unop)) ≫
    (((restrictUnderlyingIsoPostcompose g).inv.app ((pushforward f).obj F)).hom.app V)

private theorem sectionInv_naturality (sq : IsPullback h f' f g) (F : X.Modules)
    {U V : (smallEtaleSite Y')ᵒᵖ} (a : U ⟶ V) :
    ((ToInternal.underlying (structureSheaf Y')).obj
        ((pushforward f').obj ((restrictFunctor h).obj F))).obj.map a ≫ sectionInv sq F V =
      sectionInv sq F U ≫
        ((ToInternal.underlying (structureSheaf Y')).obj
          ((restrictFunctor g).obj ((pushforward f).obj F))).obj.map a := sorry

private def sectionInvUnderlying (sq : IsPullback h f' f g) (F : X.Modules) :
    (ToInternal.underlying (structureSheaf Y')).obj
        ((pushforward f').obj ((restrictFunctor h).obj F)) ⟶
      (ToInternal.underlying (structureSheaf Y')).obj
        ((restrictFunctor g).obj ((pushforward f).obj F)) :=
  InducedCategory.homMk
    { app := sectionInv sq F
      naturality := fun _ _ a ↦ sectionInv_naturality sq F a }

private theorem sectionInv_add (sq : IsPullback h f' f g) (F : X.Modules)
    (V : (smallEtaleSite Y')ᵒᵖ)
    (x y : ((pushforward f').obj ((restrictFunctor h).obj F)).val.obj V) :
    underlyingApp (structureSheaf Y') (sectionInvUnderlying sq F) V (x + y) =
      underlyingApp (structureSheaf Y') (sectionInvUnderlying sq F) V x +
        underlyingApp (structureSheaf Y') (sectionInvUnderlying sq F) V y := sorry

private theorem sectionInv_smul (sq : IsPullback h f' f g) (F : X.Modules)
    (V : (smallEtaleSite Y')ᵒᵖ) (r : (structureSheaf Y').obj.obj V)
    (x : ((pushforward f').obj ((restrictFunctor h).obj F)).val.obj V) :
    underlyingApp (structureSheaf Y') (sectionInvUnderlying sq F) V (r • x) =
      r • underlyingApp (structureSheaf Y') (sectionInvUnderlying sq F) V x := sorry

private def moduleInv (sq : IsPullback h f' f g) (F : X.Modules) :
    (pushforward f').obj ((restrictFunctor h).obj F) ⟶
      (restrictFunctor g).obj ((pushforward f).obj F) :=
  homOfUnderlying (structureSheaf Y') (sectionInvUnderlying sq F)
    (sectionInv_add sq F) (sectionInv_smul sq F)

private def moduleHom (sq : IsPullback h f' f g) :
    pushforward f ⋙ restrictFunctor g ⟶ restrictFunctor h ⋙ pushforward f' :=
  Functor.whiskerLeft (pushforward f) (restrictFunctorIsoPullback g).hom ≫
    baseChange sq.w ≫
    Functor.whiskerRight (restrictFunctorIsoPullback h).inv (pushforward f')

private theorem moduleHom_inv_id (sq : IsPullback h f' f g) (F : X.Modules) :
    (moduleHom sq).app F ≫ moduleInv sq F = 𝟙 _ := sorry

private theorem moduleInv_hom_id (sq : IsPullback h f' f g) (F : X.Modules) :
    moduleInv sq F ≫ (moduleHom sq).app F = 𝟙 _ := sorry

private def moduleIso (sq : IsPullback h f' f g) (F : X.Modules) :
    (restrictFunctor g).obj ((pushforward f).obj F) ≅
      (pushforward f').obj ((restrictFunctor h).obj F) where
  hom := (moduleHom sq).app F
  inv := moduleInv sq F
  hom_inv_id := moduleHom_inv_id sq F
  inv_hom_id := moduleInv_hom_id sq F

private def moduleCochainIso (sq : IsPullback h f' f g) (C : CochainComplex X.Modules ℤ) :
    ((restrictFunctor g).mapHomologicalComplex (up ℤ)).obj
        (((pushforward f).mapHomologicalComplex (up ℤ)).obj C) ≅
      ((pushforward f').mapHomologicalComplex (up ℤ)).obj
        (((restrictFunctor h).mapHomologicalComplex (up ℤ)).obj C) :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ moduleIso sq (C.X n))
    (fun a b _ ↦ ((moduleHom sq).naturality (C.d a b)).symm)

private def exactPullbackIsoRestriction {T U : AlgebraicSpace S} (q : U ⟶ T) [Etale q] :
    (pullback q).mapDerivedCategory ≅ restrictFunctorDerived q :=
  Localization.liftNatIso (DerivedCategory.Q (C := T.Modules))
    (HomologicalComplex.quasiIso T.Modules (up ℤ))
    (DerivedCategory.Q ⋙ (pullback q).mapDerivedCategory)
    (DerivedCategory.Q ⋙ restrictFunctorDerived q)
    (pullback q).mapDerivedCategory (restrictFunctorDerived q)
    ((pullback q).mapDerivedCategoryFactors ≪≫
      Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex (restrictFunctorIsoPullback q).symm (up ℤ))
        DerivedCategory.Q ≪≫ (restrictFunctor q).mapDerivedCategoryFactors.symm)

/-- Total derived pullback along an étale morphism is exact étale restriction. -/
def pullbackIsoRestriction {T U : AlgebraicSpace S} (q : U ⟶ T) [Etale q] :
    Functor.LeftDerived.Homotopy.functor (pullback q) ≅ restrictFunctorDerived q :=
  (ModuleDerived.pullbackIsoTotalLeftDerived q).symm ≪≫
    ModuleDerived.pullbackIsoMapDerivedCategory q ≪≫ exactPullbackIsoRestriction q

private theorem restrictedPushforwardAugmentation_quasiIso
    (C : CochainComplex X.Modules ℤ) :
    let I := (CochainComplex.KInjectiveResolution.Construction.replacement.{u} X.Modules).obj C
    let J := ((restrictFunctor h).mapHomologicalComplex (up ℤ)).obj I
    QuasiIso (((pushforward f').mapHomologicalComplex (up ℤ)).map
      ((CochainComplex.KInjectiveResolution.Construction.augmentation.{u} X'.Modules).app J)) :=
  sorry

private def restrictedPushforwardIso (C : CochainComplex X.Modules ℤ) :
    let I := (CochainComplex.KInjectiveResolution.Construction.replacement.{u} X.Modules).obj C
    let J := ((restrictFunctor h).mapHomologicalComplex (up ℤ)).obj I
    DerivedCategory.Q.obj (((pushforward f').mapHomologicalComplex (up ℤ)).obj J) ≅
      (moduleDerivedPushforward f').obj (DerivedCategory.Q.obj J) :=
  let I := (CochainComplex.KInjectiveResolution.Construction.replacement.{u} X.Modules).obj C
  let J := ((restrictFunctor h).mapHomologicalComplex (up ℤ)).obj I
  Localization.isoOfHom (DerivedCategory.Q (C := Y'.Modules))
      (HomologicalComplex.quasiIso Y'.Modules (up ℤ))
      (((pushforward f').mapHomologicalComplex (up ℤ)).map
        ((CochainComplex.KInjectiveResolution.Construction.augmentation.{u} X'.Modules).app J))
      (restrictedPushforwardAugmentation_quasiIso (h := h) (f' := f') C) ≪≫
    ((Functor.KInjectiveModel.fac.{u} (pushforward f')).app J).symm ≪≫
    (Functor.KInjectiveModel.isoOfModel.{u} (pushforward f')
      (moduleDerivedPushforward f') (moduleDerivedPushforward.unit f')).app
        (DerivedCategory.Q.obj J)

/-- Étale derived base change is computed by cartesian scheme-chart lifts and the
specified K-injective augmentations of the restricted complex. -/
def derivedIso (sq : IsPullback h f' f g) (E : ModuleDerived X) :
    (Hom.DerivedBaseChange.source f g).obj E ≅
      (Hom.DerivedBaseChange.target h f').obj E :=
  let C := DerivedCategory.Q.objPreimage E
  let I := (CochainComplex.KInjectiveResolution.Construction.replacement.{u} X.Modules).obj C
  (pullbackIsoRestriction g).app ((moduleDerivedPushforward f).obj E) ≪≫
    (restrictFunctorDerived g).mapIso
      ((moduleDerivedPushforward f).mapIso (DerivedCategory.Q.objObjPreimageIso E).symm ≪≫
        ((Functor.KInjectiveModel.isoOfModel.{u} (pushforward f)
          (moduleDerivedPushforward f) (moduleDerivedPushforward.unit f)).app
            (DerivedCategory.Q.obj C)).symm ≪≫
        (Functor.KInjectiveModel.fac.{u} (pushforward f)).app C) ≪≫
    (restrictFunctor g).mapDerivedCategoryFactors.app
      (((pushforward f).mapHomologicalComplex (up ℤ)).obj I) ≪≫
    DerivedCategory.Q.mapIso (moduleCochainIso sq I) ≪≫
    restrictedPushforwardIso (h := h) (f' := f') C ≪≫
    (moduleDerivedPushforward f').mapIso
      (((restrictFunctor h).mapDerivedCategoryFactors.app I).symm ≪≫
        (restrictFunctorDerived h).mapIso
          ((Functor.KInjectiveModel.inputAugmentationIso.{u} C).symm ≪≫
            DerivedCategory.Q.objObjPreimageIso E) ≪≫
        ((pullbackIsoRestriction h).app E).symm)

/-- The chart-limit construction of derived base change has the canonical mate as
its forward map. -/
theorem derivedIso_hom (sq : IsPullback h f' f g) (E : ModuleDerived X) :
    (derivedIso sq E).hom = Hom.DerivedBaseChange.app sq.toCommSq E := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.EtaleBaseChangeModel

