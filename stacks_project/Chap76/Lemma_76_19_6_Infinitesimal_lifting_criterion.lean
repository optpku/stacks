module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.Comparison
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.19.6 (Infinitesimal lifting criterion): A morphism of algebraic spaces
is smooth if and only if it is locally of finite presentation and formally
smooth. -/
@[stacks 04AM] #check
  (AlgebraicGeometry.AlgebraicSpace.Smooth.iff_locallyOfFinitePresentation_and_formallySmooth :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      Smooth f ↔ LocallyOfFinitePresentation f ∧ FormallySmooth f)
