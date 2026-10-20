module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder.Existence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.7.1: a formally unramified morphism of schemes admits a universal
first-order thickening of its source over its target. -/
@[stacks 04F3] #check
  (AlgebraicGeometry.FormallyUnramified.existsUniversalFirstOrderThickening :
    ∀ {X Z : AlgebraicGeometry.Scheme.{u}} (h : Z ⟶ X)
      [AlgebraicGeometry.FormallyUnramified h],
      ∃ T : AlgebraicGeometry.Thickening.Over X,
        T.left = Over.mk h ∧ AlgebraicGeometry.Thickening.IsUniversalFirstOrder T)
