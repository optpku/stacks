module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Definition 67.37.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is smooth if the equivalent conditions of Lemma 67.22.1 hold with `P` = smooth. -/
@[stacks 03ZC] #check (AlgebraicGeometry.AlgebraicSpace.Smooth :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), Prop)

/- Definition 67.37.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is smooth at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X` of `x` has
smooth restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 03ZC] #check (AlgebraicGeometry.AlgebraicSpace.SmoothAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : AlgebraicGeometry.AlgebraicSpace.Points X), Prop)
