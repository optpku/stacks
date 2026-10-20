module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.GUnramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Local
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 67.38.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is unramified if the equivalent conditions of Lemma 67.22.1 hold with `P` = unramified. -/
@[stacks 03ZH] #check (AlgebraicGeometry.AlgebraicSpace.Unramified :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)

/- Definition 67.38.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is unramified at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X` of `x` has
unramified restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 03ZH] #check (AlgebraicGeometry.AlgebraicSpace.UnramifiedAt :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) (x : AlgebraicGeometry.AlgebraicSpace.Points X), Prop)

/- Definition 67.38.1 (3): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is G-unramified if the equivalent conditions of Lemma 67.22.1 hold with `P` = G-unramified. -/
@[stacks 03ZH] #check (AlgebraicGeometry.AlgebraicSpace.GUnramified :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)

/- Definition 67.38.1 (4): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is G-unramified at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X` of `x` has
G-unramified restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 03ZH] #check (AlgebraicGeometry.AlgebraicSpace.GUnramifiedAt :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) (x : AlgebraicGeometry.AlgebraicSpace.Points X), Prop)
