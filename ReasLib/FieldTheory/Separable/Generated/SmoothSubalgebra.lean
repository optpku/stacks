module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Separable.Generated.Properties

/-!
# Smooth subalgebra models of separable field extensions

This leaf owns the reusable relation between separability in the
Stacks-project sense and smooth subalgebras with a fixed ambient fraction
field.  Finite-set and directed-family forms are included because they are
the natural downstream interface for approximation arguments.

@stack 037X
@stack 07BV
-/

@[expose] public section

namespace Algebra.IsSeparableOver

universe u v

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- A field extension with a smooth subalgebra whose fraction field is the
ambient field is separable over its base. -/
@[stacks 037X "smooth fraction-field model implies separability"]
theorem of_smooth_subalgebra_isFractionRing
    (A : Subalgebra k K) (hA : Algebra.Smooth k A) (hfrac : IsFractionRing A K) :
    Algebra.IsSeparableOver k K := sorry

/-- An essentially finite-type separable field extension has a smooth
subalgebra whose fraction field is the ambient field. -/
@[stacks 037X "separable extensions admit smooth fraction-field models"]
theorem exists_smooth_subalgebra_isFractionRing
    [Algebra.EssFiniteType k K] [Algebra.IsSeparableOver k K] :
    ∃ A : Subalgebra k K, Algebra.Smooth k A ∧ IsFractionRing A K := sorry

/-- Explicit-hypothesis form of `exists_smooth_subalgebra_isFractionRing`; use this when
separability is available as a proposition value rather than an installed instance. -/
@[stacks 037X "explicit smooth fraction-field model bridge"]
theorem exists_smooth_subalgebra_isFractionRing_of [Algebra.EssFiniteType k K]
    (hsep : Algebra.IsSeparableOver k K) :
    ∃ A : Subalgebra k K, Algebra.Smooth k A ∧ IsFractionRing A K := sorry

/-- An essentially finite-type field extension is separable over its base
exactly when it has a smooth subalgebra with the given fraction field. -/
@[stacks 037X]
theorem iff_exists_smooth_subalgebra_isFractionRing [Algebra.EssFiniteType k K] :
    Algebra.IsSeparableOver k K ↔
      ∃ A : Subalgebra k K, Algebra.Smooth k A ∧ IsFractionRing A K := sorry

/-- Every finite subset of a separable field extension lies in a smooth
subalgebra over the base field. -/
@[stacks 07BV "finite smooth subalgebra cover"]
theorem exists_smooth_subalgebra_containing_finset [Algebra.IsSeparableOver k K]
    (E : Finset K) :
    ∃ A : Subalgebra k K, Algebra.Smooth k A ∧ (E : Set K) ⊆ A := sorry

/-- Explicit-hypothesis form of `exists_smooth_subalgebra_containing_finset`; this avoids
installing a proposition-valued separability witness solely for the call. -/
@[stacks 07BV "explicit finite smooth-cover bridge"]
theorem exists_smooth_subalgebra_containing_finset_of
    (hsep : Algebra.IsSeparableOver k K) (E : Finset K) :
    ∃ A : Subalgebra k K, Algebra.Smooth k A ∧ (E : Set K) ⊆ A := sorry

/-- A separable field extension is the directed supremum of a nonempty family
of smooth subalgebras. -/
@[stacks 07BV "directed smooth subalgebra family"]
theorem exists_directed_smooth_subalgebra_family [Algebra.IsSeparableOver k K] :
    ∃ (ι : Type (max u v)) (S : ι → Subalgebra k K), Nonempty ι ∧
      Directed (· ≤ ·) S ∧ (∀ i, Algebra.Smooth k (S i)) ∧
        iSup S = (⊤ : Subalgebra k K) := sorry

/-- Explicit-hypothesis form of `exists_directed_smooth_subalgebra_family`; this keeps a
one-off separability proof out of local instance search. -/
@[stacks 07BV "explicit directed smooth-family bridge"]
theorem exists_directed_smooth_subalgebra_family_of
    (hsep : Algebra.IsSeparableOver k K) :
    ∃ (ι : Type (max u v)) (S : ι → Subalgebra k K), Nonempty ι ∧
      Directed (· ≤ ·) S ∧ (∀ i, Algebra.Smooth k (S i)) ∧
        iSup S = (⊤ : Subalgebra k K) := sorry

end Algebra.IsSeparableOver
