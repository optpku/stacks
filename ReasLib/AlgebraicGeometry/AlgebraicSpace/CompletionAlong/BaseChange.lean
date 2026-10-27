/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.ComplementMap
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale.BaseChange
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale.FiniteType

/-!
# Completion and base change

Base change preserves the categories of locally finite type algebraic spaces
isomorphic over an open complement and locally Noetherian rig-étale formal
spaces. The canonical comparison between completing a base change and base
changing a completion is invertible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits Opposite
open TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

private theorem isIsoOverOpen_of_factors {S : Scheme.{u}}
    {X Y U V : AlgebraicSpace S} (f : X ⟶ Y) (ι : U ⟶ Y) (ι' : V ⟶ Y)
    [IsOpenImmersion ι] [IsOpenImmersion ι'] (j : U ⟶ V) (hj : j ≫ ι' = ι)
    (hf : IsIsoOverOpen f ι') : IsIsoOverOpen f ι := by
  let p := openInverseImage_isPullback f ι
  let q := openInverseImage_isPullback f ι'
  let a := q.lift (openInverseImageι f ι) (openInverseImageTo f ι ≫ j)
    (by rw [Category.assoc, hj]; exact p.w)
  have outer : IsPullback (a ≫ openInverseImageι f ι')
      (openInverseImageTo f ι) f (j ≫ ι') := by
    rw [show a ≫ openInverseImageι f ι' = openInverseImageι f ι from
      q.lift_fst _ _ _, hj]
    exact p
  have w : a ≫ openInverseImageTo f ι' = openInverseImageTo f ι ≫ j :=
    q.lift_snd _ _ _
  exact (outer.of_right w q).isIso_snd_of_isIso hf

/-- Base change along `h : X1 ⟶ X` preserves being locally of finite type and an
isomorphism over the complementary open of `T`. -/
theorem sourceBaseChange_mem {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) :
    locallyOfFiniteTypeIsoOverOpenProperty
        (openComplementι X1 (T.preimage (Points.continuous_map h)))
        ((overPullback h).obj Y.obj) :=
  by
    refine ⟨LocallyOfFiniteType.of_isPullback
      (ReasLibPullback.isPullback Y.obj.hom h) Y.property.1, ?_⟩
    let q := openInverseImage_isPullback h (openComplementι X T)
    let j := q.lift (openComplementι X1 (T.preimage (Points.continuous_map h)))
      (openComplementAlong.map h T) (by rfl)
    refine isIsoOverOpen_of_factors (overPullbackSnd h Y.obj)
      (openComplementι X1 (T.preimage (Points.continuous_map h)))
      (openInverseImageι h (openComplementι X T)) j (q.lift_fst _ _ _) ?_
    exact IsoOverOpen.baseChange_mem h (openComplementι X T)
      ⟨Y.obj, Y.property.2⟩

/-- Base change along `h : X1 ⟶ X` as a functor `Source X T ⥤ Source X1 T1`,
where `T1` is the inverse image of `T` on `X1`. -/
def sourceBaseChange {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) :
    Source X T ⥤ Source X1 (T.preimage (Points.continuous_map h)) :=
  ObjectProperty.lift
    (locallyOfFiniteTypeIsoOverOpenProperty
      (openComplementι X1 (T.preimage (Points.continuous_map h))))
    (LocallyOfFiniteTypeIsoOverOpen.inclusion (openComplementι X T) ⋙ overPullback h)
    (fun Y ↦ sourceBaseChange_mem h T Y)

/-- After inclusion into the slice, `sourceBaseChange` is ordinary slice base
change along `h`. -/
theorem sourceBaseChange_obj {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) :
    ((sourceBaseChange h T).obj Y).obj = Over.mk (overPullbackSnd h Y.obj) :=
  rfl

/-- On morphisms, `sourceBaseChange` is the induced map of fibre products. -/
theorem sourceBaseChange_hom {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) {Y Y' : Source X T} (φ : Y ⟶ Y') :
    ((sourceBaseChange h T).map φ).hom.left = overPullbackMap h φ.hom :=
  rfl

/-- Base change along `map h T` preserves being a locally Noetherian rig-étale
morphism of formal algebraic spaces. -/
theorem targetBaseChange_mem {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (W : Target X T) :
    FormalAlgebraicSpace.isLocallyNoetherianRigEtaleOver
        (completionAlong X1 (T.preimage (Points.continuous_map h)))
        ((Over.pullback (map h T)).obj W.obj) :=
  by
    rcases W.property with ⟨hW, hX, hNW, hNX, hg⟩
    letI := hW
    letI := hX
    letI := hNW
    letI := hNX
    letI := hg
    change FormalAlgebraicSpace.IsLocallyNoetherianRigEtale
      (pullback.snd W.obj.hom (map h T))
    refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    exact FormalAlgebraicSpace.RigEtale.pullback_snd W.obj.hom (map h T)
      (representableByAlgebraicSpaces_completionAlong_map h T)

/-- Base change along `map h T : X1_/T1 ⟶ X_/T` as a functor
`Target X T ⥤ Target X1 T1`. -/
def targetBaseChange {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) :
    Target X T ⥤ Target X1 (T.preimage (Points.continuous_map h)) :=
  ObjectProperty.lift
    (FormalAlgebraicSpace.isLocallyNoetherianRigEtaleOver
      (completionAlong X1 (T.preimage (Points.continuous_map h))))
    (FormalAlgebraicSpace.LocallyNoetherianRigEtaleOver.inclusion (completionAlong X T) ⋙
      Over.pullback (map h T))
    (fun W ↦ targetBaseChange_mem h T W)

/-- The structure morphism of a `targetBaseChange` object is the second
projection of the functor-category pullback along `map h T`. -/
theorem targetBaseChange_obj {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (W : Target X T) :
    ((targetBaseChange h T).obj W).obj.hom = pullback.snd W.obj.hom (map h T) :=
  rfl

/-- On morphisms, `targetBaseChange` is `Over.pullback (map h T)`. -/
theorem targetBaseChange_hom {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) {W W' : Target X T} (ψ : W ⟶ W') :
    ((targetBaseChange h T).map ψ).hom = (Over.pullback (map h T)).map ψ.hom :=
  rfl


private theorem mapsInto_app_preimage_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (T : Closeds (Points Y))
    {U : (Over S)ᵒᵖ} (x : X.functorOfPoints.obj U) :
    mapsInto (T : Set (Points Y)) (f.app U x) ↔
      mapsInto (T.preimage (Points.continuous_map f) : Set (Points X)) x := by
  have hcomp (p : U.unop.left) :
      Points.mapOfOver (yonedaEquiv.symm (f.app U x) : ofOver U.unop ⟶ Y) p =
        Points.map f (Points.mapOfOver (yonedaEquiv.symm x : ofOver U.unop ⟶ X) p) := by
    rw [← yonedaEquiv_symm_naturality_right]
    exact @Points.map_comp S (ofOver U.unop) X Y (yonedaEquiv.symm x) f _
  simp only [mapsInto, Set.range_subset_iff, hcomp, Closeds.coe_preimage, Set.mem_preimage]

/-- The first projection of the completed fibre product `Y ×_X X1` along the
inverse image of `T`. -/
def completedPullbackFst {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) :
    completionAlong (overPullbackObj h Y.obj)
        ((T.preimage (Points.continuous_map h)).preimage
          (Points.continuous_map (overPullbackSnd h Y.obj))) ⟶
      completionAlong Y.obj.left (T.preimage (Points.continuous_map Y.obj.hom)) where
  app U := ofHom fun x ↦ ⟨(overPullbackFst h Y.obj).app U x.1, by
    apply (mapsInto_app_preimage_iff Y.obj.hom T _).mp
    have hw : Y.obj.hom.app U ((overPullbackFst h Y.obj).app U x.1) =
        h.app U ((overPullbackSnd h Y.obj).app U x.1) :=
      congrArg (fun k ↦ k.app U x.1)
        (pullback.condition (C := (Over S)ᵒᵖ ⥤ Type u) (f := Y.obj.hom) (g := h))
    change mapsInto (T : Set (Points X))
      (Y.obj.hom.app U ((overPullbackFst h Y.obj).app U x.1))
    exact hw.symm ▸ mapsInto_comp h T
      (mapsInto_comp (overPullbackSnd h Y.obj)
        (T.preimage (Points.continuous_map h)) x.2)⟩
  naturality := by
    intro U V φ
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k :
        (overPullbackObj h Y.obj).functorOfPoints.obj U ⟶
          Y.obj.left.functorOfPoints.obj V ↦ k x.1)
      ((overPullbackFst h Y.obj).naturality φ)

/-- Components of `completedPullbackFst` are the first projections of
`Y ×_X X1`. -/
theorem completedPullbackFst_app {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) (U : (Over S)ᵒᵖ)
    (x : (completionAlong (overPullbackObj h Y.obj)
        ((T.preimage (Points.continuous_map h)).preimage
          (Points.continuous_map (overPullbackSnd h Y.obj)))).obj U) :
    (ι Y.obj.left (T.preimage (Points.continuous_map Y.obj.hom))).app U
        ((completedPullbackFst h T Y).app U x) =
      (overPullbackFst h Y.obj).app U
        ((ι (overPullbackObj h Y.obj)
            ((T.preimage (Points.continuous_map h)).preimage
              (Points.continuous_map (overPullbackSnd h Y.obj)))).app U x) :=
  rfl

/-- The completed first and second projections of `Y ×_X X1` form a cone over
`map Y.obj.hom T` and `map h T`. -/
theorem completedPullback_condition {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) :
    completedPullbackFst h T Y ≫ map Y.obj.hom T =
      map (overPullbackSnd h Y.obj) (T.preimage (Points.continuous_map h)) ≫
        map h T :=
  by
    ext U x
    apply Subtype.ext
    exact congrArg (fun k ↦ k.app U x.1)
      (pullback.condition (C := (Over S)ᵒᵖ ⥤ Type u) (f := Y.obj.hom) (g := h))

/-- The mediating morphism from the completed fibre product `Y ×_X X1` to the
chosen pullback of the completed structure maps. -/
def completedPullbackComparison {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) :
    completionAlong (overPullbackObj h Y.obj)
        ((T.preimage (Points.continuous_map h)).preimage
          (Points.continuous_map (overPullbackSnd h Y.obj))) ⟶
      pullback (map Y.obj.hom T) (map h T) :=
  pullback.lift (completedPullbackFst h T Y)
    (map (overPullbackSnd h Y.obj) (T.preimage (Points.continuous_map h)))
    (completedPullback_condition h T Y)

/-- Postcomposing `completedPullbackComparison` with the second projection
recovers completion of `overPullbackSnd`. -/
theorem completedPullbackComparison_snd {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) :
    completedPullbackComparison h T Y ≫ pullback.snd (map Y.obj.hom T) (map h T) =
      map (overPullbackSnd h Y.obj) (T.preimage (Points.continuous_map h)) :=
  by
    exact pullback.lift_snd _ _ _

/-- Completing the fibre product `Y ×_X X1` along the inverse image of `T`
exhibits a pullback of the completed structure maps. -/
theorem isPullback_completionAlong_pullback {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) :
    IsPullback (completedPullbackFst h T Y)
      (map (overPullbackSnd h Y.obj) (T.preimage (Points.continuous_map h)))
      (map Y.obj.hom T) (map h T) :=
  by
    have hf : completedPullbackFst h T Y ≫
        ι Y.obj.left (T.preimage (Points.continuous_map Y.obj.hom)) =
        ι (overPullbackObj h Y.obj)
          ((T.preimage (Points.continuous_map h)).preimage
            (Points.continuous_map (overPullbackSnd h Y.obj))) ≫
          overPullbackFst h Y.obj := by
      ext U x
      rfl
    have hh : map h T ≫ ι X T =
        ι X1 (T.preimage (Points.continuous_map h)) ≫ h := by
      ext U x
      rfl
    have outer :=
      (completionAlong_isPullback (overPullbackSnd h Y.obj)
        (T.preimage (Points.continuous_map h))).paste_horiz
          (IsPullback.of_hasPullback (C := (Over S)ᵒᵖ ⥤ Type u) Y.obj.hom h)
    refine IsPullback.of_right ?_ (completedPullback_condition h T Y)
      (completionAlong_isPullback Y.obj.hom T)
    rw [hf, hh]
    exact outer

/-- The canonical 2-cell of the completion/base-change square, with components
the mediating maps from completed fibre products into chosen formal pullbacks. -/
def baseChangeHom {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) :
    sourceBaseChange h T ⋙ completionFunctor X1 (T.preimage (Points.continuous_map h)) ⟶
      completionFunctor X T ⋙ targetBaseChange h T where
  app Y :=
    ObjectProperty.homMk
      (Over.homMk (completedPullbackComparison h T Y) (completedPullbackComparison_snd h T Y))
  naturality := by
    intro Y Y' φ
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    change mapOver (T.preimage (Points.continuous_map h))
        ((overPullback h).map φ.hom) ≫ completedPullbackComparison h T Y' =
      completedPullbackComparison h T Y ≫
        pullback.lift (pullback.fst (map Y.obj.hom T) (map h T) ≫ mapOver T φ.hom)
          (pullback.snd (map Y.obj.hom T) (map h T)) _
    unfold completedPullbackComparison
    apply pullback.hom_ext
    · erw [Category.assoc, pullback.lift_fst, Category.assoc,
        pullback.lift_fst, pullback.lift_fst_assoc]
      ext U x
      apply Subtype.ext
      exact congrArg (fun k :
          (overPullbackObj h Y.obj).functorOfPoints ⟶ Y'.obj.left.functorOfPoints ↦
            k.app U x.1)
        (show overPullbackMap h φ.hom ≫ overPullbackFst h Y'.obj =
            overPullbackFst h Y.obj ≫ φ.hom.left from
          ReasLibPullback.pullbackLift_fst Y'.obj.hom h
            (overPullbackFst h Y.obj ≫ φ.hom.left) (overPullbackSnd h Y.obj)
            (overPullback_fst_comp h φ.hom))
    · erw [Category.assoc, pullback.lift_snd, Category.assoc,
        pullback.lift_snd, pullback.lift_snd]
      ext U x
      apply Subtype.ext
      exact congrArg (fun k :
          (overPullbackObj h Y.obj).functorOfPoints ⟶ X1.functorOfPoints ↦
            k.app U x.1)
        (show overPullbackMap h φ.hom ≫ overPullbackSnd h Y'.obj =
            overPullbackSnd h Y.obj from
          ReasLibPullback.pullbackLift_snd Y'.obj.hom h
            (overPullbackFst h Y.obj ≫ φ.hom.left) (overPullbackSnd h Y.obj)
            (overPullback_fst_comp h φ.hom))

/-- The component of `baseChangeHom` is the mediating morphism
`completedPullbackComparison`. -/
theorem baseChangeHom_app {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) :
    ((baseChangeHom h T).app Y).hom.left = completedPullbackComparison h T Y :=
  rfl


/-- Completion commutes with base change: the canonical comparison from the
completion of an algebraic-space base change to the base change of its
completion is an isomorphism. -/
instance instIsIso_baseChangeHom {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) : IsIso (baseChangeHom h T) :=
  by
    haveI (Y : Source X T) : IsIso ((baseChangeHom h T).app Y) := by
      let e := (isPullback_completionAlong_pullback h T Y).isoPullback
      have he : completedPullbackComparison h T Y = e.hom := by
        apply pullback.hom_ext
        · exact (pullback.lift_fst _ _ _).trans
            (isPullback_completionAlong_pullback h T Y).isoPullback_hom_fst.symm
        · exact (pullback.lift_snd _ _ _).trans
            (isPullback_completionAlong_pullback h T Y).isoPullback_hom_snd.symm
      haveI : IsIso (completedPullbackComparison h T Y) := by
        rw [he]
        infer_instance
      haveI : IsIso ((Over.forget _).map ((baseChangeHom h T).app Y).hom) := by
        change IsIso (completedPullbackComparison h T Y)
        infer_instance
      exact (ObjectProperty.isIso_hom_iff _).mp
        (isIso_of_reflects_iso _ (Over.forget _))
    exact NatIso.isIso_of_isIso_app (baseChangeHom h T)

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
