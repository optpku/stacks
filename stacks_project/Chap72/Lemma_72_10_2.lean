module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme.FieldExtension
import StacksCheckRecall

/-!
# Schematic locus after field extension

A quasi-separated algebraic space over a field that becomes a scheme after some
field-extension base change remains a scheme after base change to the algebraic
closure, and if it is also quasi-compact then it becomes a scheme after a finite
separable extension.

Each check supplies an arbitrary field extension and its scheme-base-change
hypothesis. By existential elimination, this is equivalent to assuming the
existence of such an extension in each source implication.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CommRingCat

universe u

/- Lemma 72.10.2 (1): A quasi-separated algebraic space that becomes a scheme
after a field extension becomes a scheme over the algebraic closure. -/
@[stacks 0B84] #check
  (AlgebraicGeometry.AlgebraicSpace.IsScheme.of_baseChange_algebraicClosure :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      (X : AlgebraicSpace (Spec (CommRingCat.of k))) [IsAbsolutelyQuasiSeparated X],
      IsScheme (AlgebraicSpace.baseChange (FieldExtension.specMap k K) X) →
      IsScheme (AlgebraicSpace.baseChange
        (FieldExtension.specMap k (AlgebraicClosure k)) X))

/- Lemma 72.10.2 (2): A quasi-compact quasi-separated algebraic space that becomes
a scheme after a field extension becomes a scheme over a finite separable extension. -/
@[stacks 0B84] #check
  (AlgebraicGeometry.AlgebraicSpace.IsScheme.exists_finiteSeparable_of_baseChange :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      (X : AlgebraicSpace (Spec (CommRingCat.of k)))
      [IsAbsolutelyQuasiSeparated X] [IsQuasiCompact X],
      IsScheme (AlgebraicSpace.baseChange (FieldExtension.specMap k K) X) →
      ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
        (_ : FiniteDimensional k k') (_ : Algebra.IsSeparable k k'),
        IsScheme (AlgebraicSpace.baseChange (FieldExtension.specMap k k') X))
