/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 30.26.1: properness of the reduced induced closed subscheme, of some closed-subscheme
structure, and of every closed-subscheme structure on a fixed closed subset are equivalent. -/
@[stacks 0CYL] #check
  (AlgebraicGeometry.ClosedSubset.isProperOver_tfae :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.LocallyOfFiniteType f] (Z : TopologicalSpace.Closeds X),
      List.TFAE [
        AlgebraicGeometry.ClosedSubset.IsProperOver f Z,
        ∃ T : AlgebraicGeometry.Scheme.ClosedSubschemeStructure Z,
          AlgebraicGeometry.IsProper (T.ι ≫ f),
        ∀ T : AlgebraicGeometry.Scheme.ClosedSubschemeStructure Z,
          AlgebraicGeometry.IsProper (T.ι ≫ f)])
