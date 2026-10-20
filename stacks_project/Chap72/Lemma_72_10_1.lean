module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme.PurelyInseparable
import StacksCheckRecall

/-!
# Schemes after purely inseparable field base change

An algebraic space over a field that becomes a scheme after base change along a
purely inseparable field extension is itself a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CommRingCat

universe u

/- Lemma 72.10.1: An algebraic space over a field is a scheme if it becomes
a scheme after base change to some purely inseparable field extension. -/
@[stacks 0B83] #check
  (AlgebraicGeometry.AlgebraicSpace.IsScheme.of_baseChange_isPurelyInseparable :
    ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (CommRingCat.of k))),
      (∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
        (_ : IsPurelyInseparable k k'),
        IsScheme (AlgebraicSpace.baseChange (FieldExtension.specMap k k') X)) → IsScheme X)
