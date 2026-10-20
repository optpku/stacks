module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.Point
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- Lemma 71.15.2: the scheme-theoretic fibre over a scheme point. -/
#check (AlgebraicGeometry.AlgebraicSpace.fiber :
  ∀ {Y : Scheme.{u}} {X : AlgebraicSpace Y},
    (X ⟶ AlgebraicGeometry.AlgebraicSpace.ofOver (Over.mk (𝟙 Y))) →
      Y → AlgebraicSpace Y)

#check (AlgebraicGeometry.AlgebraicSpace.fiber_eq_pullback :
  ∀ {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ AlgebraicGeometry.AlgebraicSpace.ofOver (Over.mk (𝟙 Y))) (y : Y),
    AlgebraicGeometry.AlgebraicSpace.fiber f y =
      pullback f (AlgebraicGeometry.AlgebraicSpace.residueFieldHom Y y))

#check (CategoryTheory.IsPullback.of_hasPullback :
  ∀ {C : Type u} [Category.{u} C] {X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g],
    IsPullback (pullback.fst f g) (pullback.snd f g) f g)
