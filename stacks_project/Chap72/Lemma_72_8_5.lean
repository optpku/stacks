module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Alteration
import StacksCheckRecall

/-!
# Alterations inside a proper surjective morphism

A proper surjective morphism of algebraic spaces onto an integral target
restricts to an alteration along some integral closed subspace of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 72.8.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a proper
surjective morphism of algebraic spaces over `S`. Assume `Y` is integral.
Then there exists an integral closed subspace `X' ⊂ X` such that
`f' = X'.ι ≫ f : X'.X ⟶ Y` is an alteration. -/
@[stacks 0DMN] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_integralClosedSubspace_isAlteration :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsIntegral Y]
      (f : X ⟶ Y) [Proper f] [Surjective f],
    ∃ (X' : ClosedSubspace X) (hX' : IsIntegral X'.X),
      IsAlteration (X'.ι ≫ f))

end AlgebraicGeometry.AlgebraicSpace
