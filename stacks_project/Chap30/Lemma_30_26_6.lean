module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper.FiniteUnion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 30.26.6

For a locally finite type morphism of schemes, a finite union of closed subsets proper over the
base is proper over the base.
-/
@[stacks 0CYR] #check (AlgebraicGeometry.ClosedSubset.IsProperOver.iSup :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.LocallyOfFiniteType f] {ι : Type u} [Finite ι]
    (Z : ι → TopologicalSpace.Closeds X),
    (∀ i, AlgebraicGeometry.ClosedSubset.IsProperOver f (Z i)) →
      AlgebraicGeometry.ClosedSubset.IsProperOver f (iSup Z))
