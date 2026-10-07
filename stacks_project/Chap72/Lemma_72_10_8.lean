module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap72.Lemma_72_10_8_Coproduct

/-!
# Locally quasi-finite algebraic spaces over a field

For an algebraic space over a field, Stacks locally quasi-finite over that field
is equivalent to being locally of finite type of dimension zero, to being a
scheme with either of those properties, and to being isomorphic over the field
to a disjoint union of spectra of finite-dimensional local Artinian algebras.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.10.8: Let `k` be a field. Let `X` be an algebraic space over `k`.
The following are equivalent: `X` is locally quasi-finite over `k`, `X` is
locally of finite type over `k` and has dimension `0`, `X` is a scheme and is
locally quasi-finite over `k`, `X` is a scheme and is locally of finite type
over `k` and has dimension `0`, and `X` is a disjoint union of spectra of
Artinian local `k`-algebras `A` over `k` with `FiniteDimensional k A`.

Stacks locally quasi-finite over `k` is `LocallyOfFiniteType (toBase X)` and
`LocallyQuasiFinite (toBase X)`. The source writes dimension `0`; the Lean
statements use `dimension X ≤ 0` so that the empty algebraic space, whose
dimension is `⊥`, is included. The disjoint union is an isomorphism over
`Spec k` to `ofOver (SchemeOverField.sigmaSpec ι A)`. -/
@[stacks 06S0]
theorem tfae_locallyQuasiFinite_over_field {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    List.TFAE
      [ LocallyOfFiniteType (toBase X) ∧ LocallyQuasiFinite (toBase X)
      , LocallyOfFiniteType (toBase X) ∧ dimension X ≤ 0
      , IsScheme X ∧ LocallyOfFiniteType (toBase X) ∧ LocallyQuasiFinite (toBase X)
      , IsScheme X ∧ LocallyOfFiniteType (toBase X) ∧ dimension X ≤ 0
      , Nonempty (FiniteLocalArtinianCoproduct X) ] :=
  sorry

/-- For an algebraic space locally of finite type over a field, the structure
morphism is locally quasi-finite if and only if the étale-local dimension is at
most `0`. The source writes equality with `0`; `≤ 0` includes the empty space,
whose dimension is `⊥`. -/
theorem locallyQuasiFinite_iff_dimension_le_zero {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType (toBase X)] :
    LocallyQuasiFinite (toBase X) ↔ dimension X ≤ 0 :=
  sorry

/-- An algebraic space that is locally quasi-finite over a field in the Stacks
sense is a scheme. -/
instance isScheme_of_locallyQuasiFinite {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType (toBase X)] [LocallyQuasiFinite (toBase X)] :
    IsScheme X :=
  sorry

/-- An algebraic space over a field is locally quasi-finite over `k` in the
Stacks sense if and only if it admits a finite local-Artinian coproduct
presentation. -/
theorem locallyQuasiFinite_iff_finiteLocalArtinianCoproduct {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    LocallyOfFiniteType (toBase X) ∧ LocallyQuasiFinite (toBase X) ↔
      Nonempty (FiniteLocalArtinianCoproduct X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
