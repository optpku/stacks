module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber.ConnectedComponents
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.30.1 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. The function `geometricFiberComponentCount f` sending
`y` in `|Y|` to the number of connected components of the fibre `X_k`, for any
algebraically closed representative `Spec k ⟶ Y` of `y`, is well defined. -/
@[stacks 0E1B] #check
  (AlgebraicGeometry.AlgebraicSpace.geometricFiberComponentCount_eq_enatCard :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y)
      (ybar : GeometricPoint Y), ybar.image = y →
      geometricFiberComponentCount f y =
        ENat.card
          (ConnectedComponents (Points (fieldFiber f ybar.toFieldValuedPoint))))

/- Lemma 76.30.1 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `g : Y' ⟶ Y` is a morphism, then
`geometricFiberComponentCount f' = geometricFiberComponentCount f ∘ Points.map g`
where `f' : X' ⟶ Y'` is the base change of `f`. -/
@[stacks 0E1B] #check
  (AlgebraicGeometry.AlgebraicSpace.geometricFiberComponentCount_baseChange :
    ∀ {S : Scheme.{u}} {X Y Y' X' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y)
      (g' : X' ⟶ X) (f' : X' ⟶ Y'), IsPullback g' f' f g →
      geometricFiberComponentCount f' =
        geometricFiberComponentCount f ∘ Points.map g)
