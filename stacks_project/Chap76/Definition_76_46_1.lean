module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.PseudoCoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 76.46.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is pseudo-coherent if the equivalent conditions of Lemma 67.22.1 hold with `P` = pseudo-coherent. -/
@[stacks 06BR] #check (AlgebraicGeometry.AlgebraicSpace.PseudoCoherent :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)

/- Definition 76.46.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is pseudo-coherent at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X` of `x` has
pseudo-coherent restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 06BR] #check (AlgebraicGeometry.AlgebraicSpace.PseudoCoherentAt :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y), AlgebraicGeometry.AlgebraicSpace.Points X → Prop)
