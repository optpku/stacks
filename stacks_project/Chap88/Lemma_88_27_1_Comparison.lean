module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import stacks_project.Chap88.Lemma_88_27_1_BaseChange

/-!
# Comparison 2-cell for completion versus base change

The completion of an algebraic-space fibre product along a closed subset maps
to the functor-category pullback of the completed morphisms. This is the
canonical 2-cell of the square with horizontals `functor` and verticals
`sourceBaseChange` / `targetBaseChange`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits Opposite
open TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

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
  naturality := sorry

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
    sourceBaseChange h T ⋙ functor X1 (T.preimage (Points.continuous_map h)) ⟶
      functor X T ⋙ targetBaseChange h T where
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

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
