module

public import stacks_project.Chap81.Lemma_81_11_2_Instances
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalGlueing
open CategoryTheory

universe u

/- Lemma 81.11.2: In Situation 81.10.6 the functor (81.11.0.1) reflects
isomorphisms. -/
@[stacks 0AF5] #check
  (functor_reflectsIsomorphisms :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
      [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
      [IsFormalGlueing f i],
      (functor f i).ReflectsIsomorphisms)
