module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.FinitePresentation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 37.60.5: A pseudo-coherent morphism is locally of finite presentation. -/
@[stacks 0682] #check
  (AlgebraicGeometry.PseudoCoherent.locallyOfFinitePresentation :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [PseudoCoherent f], LocallyOfFinitePresentation f)
