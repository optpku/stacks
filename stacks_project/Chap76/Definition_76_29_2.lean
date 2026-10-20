module

public import stacks_project.Chap76.Lemma_76_29_1
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 76.29.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `y` be a point of `|Y|`. We say the fibre of
`f : X ⟶ Y` at `y` is geometrically reduced if the equivalent conditions of
Lemma 76.29.1 hold, equivalently `y ∈ geometricallyReducedFiberLocus f`. -/
@[stacks 0E08] #check
  (AlgebraicGeometry.AlgebraicSpace.geometricallyReducedFiberLocus :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Set (Points Y))

#check (AlgebraicGeometry.AlgebraicSpace.mem_geometricallyReducedFiberLocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y),
    y ∈ geometricallyReducedFiberLocus f ↔
      ∀ p : FieldValuedPoint Y, Points.mk p = y →
        GeometricallyReduced (fiberOverField f p))

#check (AlgebraicGeometry.AlgebraicSpace.geometricallyReducedFiber_tfae :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y),
    List.TFAE
      [∃ p : FieldValuedPoint Y, Points.mk p = y ∧ GeometricallyReduced (fiberOverField f p),
        ∀ p : FieldValuedPoint Y, Points.mk p = y → GeometricallyReduced (fiberOverField f p),
        ∀ p : FieldValuedPoint Y, Points.mk p = y → IsReduced (fiberOverField f p)])
