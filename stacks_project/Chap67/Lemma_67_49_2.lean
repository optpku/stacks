module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Lemma_67_49_1_FiniteComponents
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents.Noetherian
import StacksCheckRecall

/-!
# Locally Noetherian algebraic spaces have finite irreducible components on compact opens

A locally Noetherian algebraic space satisfies the equivalent conditions of
Lemma 67.49.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace HasFiniteIrreducibleComponentsOnCompactOpens

/- Lemma 67.49.2: let `S` be a scheme. Let `X` be a locally Noetherian algebraic
space over `S`. Then `X` satisfies the equivalent conditions of Lemma 67.49.1,
recorded as `HasFiniteIrreducibleComponentsOnCompactOpens X`. -/
@[stacks 0GMB] #check
  (AlgebraicGeometry.AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens.instOfIsLocallyNoetherian :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X] →
        AlgebraicGeometry.AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens X)

end HasFiniteIrreducibleComponentsOnCompactOpens

end AlgebraicGeometry.AlgebraicSpace
