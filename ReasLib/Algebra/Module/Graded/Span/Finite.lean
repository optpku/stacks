module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite homogeneous generators of internally graded modules

This leaf owns finite-generation consequences of an internal decomposition of a module.  Unlike
the homogeneous-span construction, none of these statements needs a grading on the scalar ring or
a compatible graded scalar action: a homogeneous submodule is closed under the components supplied
by `DirectSum.Decomposition` already.
-/

@[expose] public section

noncomputable section

universe uι uA uM uσ

namespace Submodule.FG

variable {ι : Type uι} [DecidableEq ι]
variable {A : Type uA} [Semiring A]
variable {M : Type uM} [AddCommMonoid M] [Module A M]
variable {σ : Type uσ} [SetLike σ M] [AddSubmonoidClass σ M]

/-- A finitely generated homogeneous submodule has a finite set of homogeneous generators.

The finite set is deliberately returned as a `Set`: this is the carrier shape used by
`Submodule.span`, while `Finset` and indexed-family views are provided as bridges below. -/
@[stacks 052N "finite homogeneous generators of a submodule"]
theorem exists_finite_homogeneous_span_eq
    (ℳ : ι → σ) [DirectSum.Decomposition ℳ]
    {P : Submodule A M} (hPfg : P.FG) (hP : P.IsHomogeneous ℳ) :
    ∃ s : Set M, s.Finite ∧
      (∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x) ∧
        Submodule.span A s = P := sorry

/-- A finitely generated homogeneous submodule has a finite `Finset` of homogeneous generators.

This is a convenience bridge for source-facing finite-generator arguments; the `Set` theorem above
is the canonical owner. -/
@[stacks 052N "finite-set homogeneous generators of a submodule"]
theorem exists_finset_homogeneous_span_eq
    (ℳ : ι → σ) [DirectSum.Decomposition ℳ]
    {P : Submodule A M} (hPfg : P.FG) (hP : P.IsHomogeneous ℳ) :
    ∃ s : Finset M,
      Submodule.span A (s : Set M) = P ∧
        ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x := sorry

end Submodule.FG

namespace Module.Finite

variable {ι : Type uι} [DecidableEq ι]
variable {A : Type uA} [Semiring A]
variable {M : Type uM} [AddCommMonoid M] [Module A M]
variable {σ : Type uσ} [SetLike σ M] [AddSubmonoidClass σ M]

/-- A finitely generated internally graded module admits a finite indexed family of homogeneous
generators.

The declaration mirrors `Module.Finite.exists_fin`; only the homogeneous-generator condition is
added, and the ambient scalar ring and module remain implicit. -/
@[stacks 052N "finite module homogeneous generators"]
theorem exists_fin_homogeneous
    (ℳ : ι → σ) [DirectSum.Decomposition ℳ]
    [Module.Finite A M] :
    ∃ n : ℕ, ∃ g : Fin n → M,
        (∀ i, SetLike.IsHomogeneousElem ℳ (g i)) ∧
          Submodule.span A (Set.range g) = ⊤ := sorry

/-- A finitely generated internally graded module admits generators together with their degrees.

The degree function is returned as explicit data rather than hidden inside
`SetLike.IsHomogeneousElem`; this is the preferred owner when downstream constructions need to
form shifts, twists, or degree-indexed maps. -/
@[stacks 052N "finite module homogeneous generators with degrees"]
theorem exists_fin_homogeneous_with_degree
    (ℳ : ι → σ) [DirectSum.Decomposition ℳ]
    [Module.Finite A M] :
    ∃ n : ℕ, ∃ g : Fin n → M, ∃ d : Fin n → ι,
        (∀ i, g i ∈ ℳ (d i)) ∧
          Submodule.span A (Set.range g) = ⊤ := sorry

/-- A finitely generated internally graded module admits a finite homogeneous `Finset` generating
the top.

This is the finite-set view of `Module.Finite.exists_fin_homogeneous`. -/
@[stacks 052N "finite module homogeneous finset generators"]
theorem exists_finset_homogeneous_span_eq_top
    (ℳ : ι → σ) [DirectSum.Decomposition ℳ]
    [Module.Finite A M] :
    ∃ s : Finset M,
      Submodule.span A (s : Set M) = ⊤ ∧
        ∀ x ∈ s, SetLike.IsHomogeneousElem ℳ x := sorry

end Module.Finite

end
