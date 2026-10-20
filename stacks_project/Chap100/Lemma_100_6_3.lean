module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact.Coproduct
import StacksCheckRecall

/-!
# Finite coproducts of quasi-compact algebraic stacks
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

universe u v

/- Lemma 100.6.3: a finite disjoint union of quasi-compact algebraic stacks is a
quasi-compact algebraic stack. -/
@[stacks 04YD] #check
  (AlgebraicGeometry.AlgebraicStack.instIsQuasiCompact_coproduct :
    ∀ {S : Scheme.{u}} {I : Type v} [Finite I] (X : I → GroupoidsOver S)
      [∀ i, AlgebraicStack (X i)] [∀ i, IsQuasiCompact (X i)],
      IsQuasiCompact (GroupoidsOver.coproduct X))
