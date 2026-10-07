module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.FieldTheory.Transcendence.PurelyTranscendental
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme

/-!
# Schemes after purely transcendental field base change

A quasi-separated algebraic space over a field that becomes a scheme after base
change along a purely transcendental field extension is itself a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- Lemma 72.10.5: Let `k` be a field. Let `X` be a quasi-separated algebraic space over `k`.
If there exists a purely transcendental field extension `K/k` such that the
base change of `X` along `FieldExtension.specMap k K` is a scheme, then `X`
is a scheme. -/
@[stacks 0B85]
theorem of_baseChange_isPurelyTranscendental {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) [IsAbsolutelyQuasiSeparated X]
    (hX : ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (_ : _root_.FieldExtension.IsPurelyTranscendental k K),
      IsScheme (baseChange (FieldExtension.specMap k K) X)) :
    IsScheme X :=
  sorry

/-- If the base change of a quasi-separated algebraic space along a purely transcendental
field extension is a scheme, then the original algebraic space is a scheme. -/
theorem of_isScheme_baseChange_isPurelyTranscendental {k K : Type u} [Field k] [Field K]
    [Algebra k K] (hK : _root_.FieldExtension.IsPurelyTranscendental k K)
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) [IsAbsolutelyQuasiSeparated X]
    (hX : IsScheme (baseChange (FieldExtension.specMap k K) X)) :
    IsScheme X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsScheme
