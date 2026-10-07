module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale.Comparison
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 76.19.4: A scheme morphism is formally étale if and only if it is formally smooth
and formally unramified. -/
@[stacks 061G] #check
  (AlgebraicGeometry.FormallyEtale.iff_formallySmooth_and_formallyUnramified :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.FormallyEtale f ↔
        AlgebraicGeometry.FormallySmooth f ∧ AlgebraicGeometry.FormallyUnramified f)
