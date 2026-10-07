module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Dimension zero algebraic spaces

An algebraic space of dimension zero that is absolutely quasi-separated, locally
of finite type over a field, or Noetherian is a separated scheme, and every
quasi-compact open subspace is affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.9.1 (1): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `X` is quasi-separated and `dimension X = 0`, then `X` is a separated scheme
and every quasi-compact open of `X` is affine. -/
@[stacks 06LZ]
theorem isAffine_of_isQuasiCompact_openSubspace_of_isAbsolutelyQuasiSeparated_of_dimension_eq_zero
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (hdim : dimension X = (0 : WithBot ℕ∞)) (U : OpenSubspace X)
    [IsQuasiCompact U.X] : IsAffine U.X :=
  sorry

/-- An absolutely quasi-separated algebraic space of dimension zero is a scheme. -/
@[stacks 06LZ]
theorem isScheme_of_isAbsolutelyQuasiSeparated_of_dimension_eq_zero
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (hdim : dimension X = (0 : WithBot ℕ∞)) : IsScheme X :=
  sorry

/-- An absolutely quasi-separated algebraic space of dimension zero is absolutely
separated. -/
@[stacks 06LZ]
theorem isAbsolutelySeparated_of_isAbsolutelyQuasiSeparated_of_dimension_eq_zero
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    (hdim : dimension X = (0 : WithBot ℕ∞)) : IsAbsolutelySeparated X :=
  sorry

/-- A quasi-compact absolutely quasi-separated algebraic space of dimension zero
is affine. -/
theorem isAffine_of_isQuasiCompact_of_isAbsolutelyQuasiSeparated_of_dimension_eq_zero
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelyQuasiSeparated X]
    [IsQuasiCompact X] (hdim : dimension X = (0 : WithBot ℕ∞)) : IsAffine X :=
  sorry

/-- Lemma 72.9.1 (2): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `X` is locally of finite type over a field `k` and `dimension X = 0`, then
`X` is a separated scheme and every quasi-compact open of `X` is affine. -/
@[stacks 06LZ]
theorem isAffine_of_isQuasiCompact_openSubspace_of_locallyOfFiniteType_field_of_dimension_eq_zero
    {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f]
    (hdim : dimension X = (0 : WithBot ℕ∞)) (U : OpenSubspace X)
    [IsQuasiCompact U.X] : IsAffine U.X :=
  sorry

/-- An algebraic space locally of finite type over a field and of dimension zero
is a scheme. -/
@[stacks 06LZ]
theorem isScheme_of_locallyOfFiniteType_field_of_dimension_eq_zero
    {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f]
    (hdim : dimension X = (0 : WithBot ℕ∞)) : IsScheme X :=
  sorry

/-- An algebraic space locally of finite type over a field and of dimension zero
is absolutely separated. -/
@[stacks 06LZ]
theorem isAbsolutelySeparated_of_locallyOfFiniteType_field_of_dimension_eq_zero
    {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f]
    (hdim : dimension X = (0 : WithBot ℕ∞)) : IsAbsolutelySeparated X :=
  sorry

/-- A quasi-compact algebraic space locally of finite type over a field and of
dimension zero is affine. -/
theorem isAffine_of_isQuasiCompact_of_locallyOfFiniteType_field_of_dimension_eq_zero
    {S : Scheme.{u}} {X : AlgebraicSpace S} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} (f : X ⟶ ofOver (Over.mk σ)) [LocallyOfFiniteType f]
    [IsQuasiCompact X] (hdim : dimension X = (0 : WithBot ℕ∞)) : IsAffine X :=
  sorry

/-- Lemma 72.9.1 (3): Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `X` is Noetherian and `dimension X = 0`, then `X` is a separated scheme and
every quasi-compact open of `X` is affine. -/
@[stacks 06LZ]
theorem isAffine_of_isQuasiCompact_openSubspace_of_isNoetherian_of_dimension_eq_zero
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (hdim : dimension X = (0 : WithBot ℕ∞)) (U : OpenSubspace X)
    [IsQuasiCompact U.X] : IsAffine U.X :=
  sorry

/-- A Noetherian algebraic space of dimension zero is a scheme. -/
@[stacks 06LZ]
theorem isScheme_of_isNoetherian_of_dimension_eq_zero
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (hdim : dimension X = (0 : WithBot ℕ∞)) : IsScheme X :=
  sorry

/-- A Noetherian algebraic space of dimension zero is absolutely separated. -/
@[stacks 06LZ]
theorem isAbsolutelySeparated_of_isNoetherian_of_dimension_eq_zero
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (hdim : dimension X = (0 : WithBot ℕ∞)) : IsAbsolutelySeparated X :=
  sorry

/-- A Noetherian algebraic space of dimension zero is affine. -/
theorem isAffine_of_isNoetherian_of_dimension_eq_zero
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (hdim : dimension X = (0 : WithBot ℕ∞)) : IsAffine X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
