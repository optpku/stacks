module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Functor

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

/-- Base change along `h : X1 ⟶ X` preserves being locally of finite type and an
isomorphism over the complementary open of `T`. -/
theorem sourceBaseChange_mem {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) :
    locallyOfFiniteTypeIsoOverOpenProperty
        (openComplementι X1 (T.preimage (Points.continuous_map h)))
        ((overPullback h).obj Y.obj) :=
  sorry

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
  sorry

/-- On morphisms, `sourceBaseChange` is the induced map of fibre products. -/
theorem sourceBaseChange_hom {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) {Y Y' : Source X T} (φ : Y ⟶ Y') :
    ((sourceBaseChange h T).map φ).hom.left = overPullbackMap h φ.hom :=
  sorry

/-- Base change along `map h T` preserves being a locally Noetherian rig-étale
morphism of formal algebraic spaces. -/
theorem targetBaseChange_mem {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (W : Target X T) :
    FormalAlgebraicSpace.isLocallyNoetherianRigEtaleOver
        (completionAlong X1 (T.preimage (Points.continuous_map h)))
        ((Over.pullback (map h T)).obj W.obj) :=
  sorry

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
  sorry

/-- On morphisms, `targetBaseChange` is `Over.pullback (map h T)`. -/
theorem targetBaseChange_hom {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) {W W' : Target X T} (ψ : W ⟶ W') :
    ((targetBaseChange h T).map ψ).hom = (Over.pullback (map h T)).map ψ.hom :=
  sorry


/-- The first projection of the completed fibre product `Y ×_X X1` along the
inverse image of `T`. -/
def completedPullbackFst {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) :
    completionAlong (overPullbackObj h Y.obj)
        ((T.preimage (Points.continuous_map h)).preimage
          (Points.continuous_map (overPullbackSnd h Y.obj))) ⟶
      completionAlong Y.obj.left (T.preimage (Points.continuous_map Y.obj.hom)) where
  app U := ofHom fun x ↦ ⟨(overPullbackFst h Y.obj).app U x.1, sorry⟩
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
  sorry

/-- The completed first and second projections of `Y ×_X X1` form a cone over
`map Y.obj.hom T` and `map h T`. -/
theorem completedPullback_condition {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) :
    completedPullbackFst h T Y ≫ map Y.obj.hom T =
      map (overPullbackSnd h Y.obj) (T.preimage (Points.continuous_map h)) ≫
        map h T :=
  sorry

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
  sorry

/-- Completing the fibre product `Y ×_X X1` along the inverse image of `T`
exhibits a pullback of the completed structure maps. -/
theorem isPullback_completionAlong_pullback {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) :
    IsPullback (completedPullbackFst h T Y)
      (map (overPullbackSnd h Y.obj) (T.preimage (Points.continuous_map h)))
      (map Y.obj.hom T) (map h T) :=
  sorry

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
  naturality := sorry

/-- The component of `baseChangeHom` is the mediating morphism
`completedPullbackComparison`. -/
theorem baseChangeHom_app {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) :
    ((baseChangeHom h T).app Y).hom.left = completedPullbackComparison h T Y :=
  sorry


/-- Completion commutes with base change: the canonical comparison from the
completion of an algebraic-space base change to the base change of its
completion is an isomorphism. -/
instance instIsIso_baseChangeHom {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) : IsIso (baseChangeHom h T) :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
