module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme

/-!
# Schematic locus after field extension

A quasi-separated algebraic space over a field that becomes a scheme after some
field-extension base change remains a scheme after base change to the algebraic
closure, and if it is also quasi-compact then it becomes a scheme after a finite
separable extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- Lemma 72.10.2 (1): Let `k` be a field with algebraic closure `AlgebraicClosure k`.
Let `X` be a quasi-separated algebraic space over `k`. If there exists a field
extension `K/k` such that the base change of `X` along `FieldExtension.specMap k K`
is a scheme, then the base change of `X` along
`FieldExtension.specMap k (AlgebraicClosure k)` is a scheme. -/
@[stacks 0B84]
theorem of_exists_baseChange_algebraicClosure {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) [IsAbsolutelyQuasiSeparated X]
    (hX : ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      IsScheme (baseChange (FieldExtension.specMap k K) X)) :
    IsScheme (baseChange (FieldExtension.specMap k (AlgebraicClosure k)) X) :=
  sorry

/-- Lemma 72.10.2 (2): Let `k` be a field. Let `X` be a quasi-compact quasi-separated
algebraic space over `k`. If there exists a field extension `K/k` such that the
base change of `X` along `FieldExtension.specMap k K` is a scheme, then there exists
a finite separable field extension `k'/k` such that the base change of `X` along
`FieldExtension.specMap k k'` is a scheme. -/
@[stacks 0B84]
theorem exists_finiteSeparable_of_exists_baseChange {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact X]
    (hX : ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      IsScheme (baseChange (FieldExtension.specMap k K) X)) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : Algebra.IsSeparable k k'),
      IsScheme (baseChange (FieldExtension.specMap k k') X) :=
  sorry

/-- If the base change of a quasi-separated algebraic space along a field extension
is a scheme, then the base change along the algebraic closure is a scheme. -/
theorem of_baseChange_algebraicClosure {k K : Type u} [Field k] [Field K]
    [Algebra k K] (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    [IsAbsolutelyQuasiSeparated X]
    (hX : IsScheme (baseChange (FieldExtension.specMap k K) X)) :
    IsScheme (baseChange (FieldExtension.specMap k (AlgebraicClosure k)) X) :=
  sorry

/-- If a quasi-compact quasi-separated algebraic space becomes a scheme after base
change along a field extension, then it becomes a scheme after base change along
some finite separable extension. -/
theorem exists_finiteSeparable_of_baseChange {k K : Type u} [Field k] [Field K]
    [Algebra k K] (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    [IsAbsolutelyQuasiSeparated X] [IsQuasiCompact X]
    (hX : IsScheme (baseChange (FieldExtension.specMap k K) X)) :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : FiniteDimensional k k') (_ : Algebra.IsSeparable k k'),
      IsScheme (baseChange (FieldExtension.specMap k k') X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsScheme
