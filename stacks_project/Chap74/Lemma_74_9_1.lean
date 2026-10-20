module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranch.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 74.9.1: Let $S$ be a scheme. Let $f : X \to Y$ be a morphism of algebraic
spaces over $S$. Let $x \in |X|$. If $f$ is flat at $x$ and $X$ is geometrically
unibranch at $x$, then $Y$ is geometrically unibranch at $f(x)$.

Consider the map of étale local rings $\mathcal{O}_{Y, f(\overline{x})} \to
\mathcal{O}_{X, \overline{x}}$. By Morphisms of Spaces, Lemma 67.30.8 this is
flat. Hence if $\mathcal{O}_{X, \overline{x}}$ has a unique minimal prime, so does
$\mathcal{O}_{Y, f(\overline{x})}$ (by going down, see Algebra, Lemma 10.39.19). -/
@[stacks 06DQ] #check
  (AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranchAt.of_flatAt :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X)
      (hf : FlatAt f x) [GeometricallyUnibranchAt X x],
      GeometricallyUnibranchAt Y (Points.map f x))
