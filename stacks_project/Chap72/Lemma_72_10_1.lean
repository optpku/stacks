module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme

/-!
# Schemes after purely inseparable field base change

An algebraic space over a field that becomes a scheme after base change along a
purely inseparable field extension is itself a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- Lemma 72.10.1: Let `k` be a field. Let `X` be an algebraic space over `k`.
If there exists a purely inseparable field extension `k'/k` such that the
base change of `X` along `FieldExtension.specMap k k'` is a scheme, then `X`
is a scheme. -/
@[stacks 0B83]
theorem of_baseChange_isPurelyInseparable {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (hX : ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k')
      (_ : IsPurelyInseparable k k'),
      IsScheme (baseChange (FieldExtension.specMap k k') X)) :
    IsScheme X :=
  sorry

/-- If the base change of an algebraic space along a purely inseparable field
extension is a scheme, then the original algebraic space is a scheme. -/
theorem of_isScheme_baseChange {k k' : Type u} [Field k] [Field k']
    [Algebra k k'] [IsPurelyInseparable k k']
    (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (hX : IsScheme (baseChange (FieldExtension.specMap k k') X)) :
    IsScheme X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsScheme
