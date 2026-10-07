module

public import stacks_project.Chap76.Lemma_76_16_8_Comparison
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.16.8: A morphism of algebraic spaces is étale if and only if it is
locally of finite presentation and formally étale. -/
@[stacks 0616] #check
  (Etale.iff_locallyOfFinitePresentation_and_formallyEtale :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      Etale f ↔ LocallyOfFinitePresentation f ∧ FormallyEtale f)
