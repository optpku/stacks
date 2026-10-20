module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.QuasiCompact
import StacksCheckRecall

/-!
# Quasi-compact field-valued representatives of a point

A point of an algebraic stack admits a quasi-compact field-valued representative
if and only if every field-valued representative of that point is quasi-compact.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

universe u

/- Lemma 100.14.1: Let `X` be an algebraic stack. Let `x ∈ |X|` be a point.
The following are equivalent: some morphism `Spec(k) ⟶ X` in the equivalence
class of `x` is quasi-compact, and any morphism `Spec(k) ⟶ X` in the
equivalence class of `x` is quasi-compact. -/
@[stacks 0DTK] #check
  (AlgebraicGeometry.AlgebraicStack.existsQuasiCompactFieldValuedPoint_iff_forall :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X),
      existsQuasiCompactFieldValuedPoint X x ↔ forallFieldValuedPointQuasiCompact X x)
