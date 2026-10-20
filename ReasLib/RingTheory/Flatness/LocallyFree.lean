module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Locally Free Modules

A module over a commutative semiring is locally free if it becomes free after localizing at elements
of a cover of `Spec R`.

## Main definitions

* `Module.LocallyFree` — locally free module.
* `Module.FiniteLocallyFree` — finite locally free module.
* `Module.FiniteLocallyFreeOfRank` — finite locally free of constant rank.
-/

universe u v w

namespace Module

section

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- An `R`-module is locally free if some standard-open cover of
`Spec R` trivializes it as a free module after localization. -/
@[stacks 00NW]
class LocallyFree : Prop where
  /-- A standard-open cover on which the localized module is free. -/
  exists_standardOpen_cover :
    ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ f ∈ s, Module.Free (Localization.Away f) (LocalizedModule.Away f M)

/-- An `R`-module is finite locally free if some standard-open
cover of `Spec R` trivializes it as a finite free module after localization. -/
@[stacks 00NW]
class FiniteLocallyFree : Prop where
  /-- A standard-open cover on which the localized module is finite free. -/
  exists_standardOpen_cover :
    ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ f ∈ s,
        Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
          Module.Finite (Localization.Away f) (LocalizedModule.Away f M)

/-- An `R`-module is finite locally free of rank `r` if some
standard-open cover identifies each localization with `(Localization.Away f)^r`. -/
@[stacks 00NW]
class FiniteLocallyFreeOfRank (r : ℕ) : Prop where
  /-- A standard-open cover on which the localized module has constant rank `r`. -/
  exists_standardOpen_cover :
    ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ f ∈ s,
        Nonempty
          ((LocalizedModule.Away f M) ≃ₗ[Localization.Away f] (Fin r → Localization.Away f))

namespace FiniteLocallyFree

/-- A finite locally free module is locally free. -/
theorem locallyFree (h : FiniteLocallyFree R M) : LocallyFree R M :=
  sorry

/-- Finite local freeness supplies local freeness to typeclass search. -/
instance instLocallyFree [FiniteLocallyFree R M] : LocallyFree R M :=
  sorry

end FiniteLocallyFree

namespace LocallyFree

/-- Local freeness transports from the target of an `R`-linear equivalence to its source. -/
theorem of_linearEquiv {N : Type w} [AddCommMonoid N] [Module R N]
    (e : M ≃ₗ[R] N) (h : LocallyFree R N) :
    LocallyFree R M := sorry

/-- Local freeness is invariant under an `R`-linear equivalence. -/
theorem iff_of_linearEquiv {N : Type w} [AddCommMonoid N] [Module R N]
    (e : M ≃ₗ[R] N) :
    LocallyFree R M ↔ LocallyFree R N := sorry

end LocallyFree

namespace FiniteLocallyFreeOfRank

/-- A finite free module is finite locally free of rank equal to its `Module.finrank`. -/
@[stacks 00NW "finite free modules are finite locally free"]
theorem of_finite_free [Module.Free R M] [Module.Finite R M] :
    FiniteLocallyFreeOfRank R M (Module.finrank R M) := sorry

/-- A finite locally free module of specified rank is finite locally free. -/
theorem finiteLocallyFree {r : ℕ} (h : FiniteLocallyFreeOfRank R M r) :
    FiniteLocallyFree R M := sorry

/-- Finite local freeness of a fixed rank transports from the target of an `R`-linear
equivalence to its source. -/
theorem of_linearEquiv {N : Type w} [AddCommMonoid N] [Module R N] {r : ℕ}
    (e : M ≃ₗ[R] N) (h : FiniteLocallyFreeOfRank R N r) :
    FiniteLocallyFreeOfRank R M r := sorry

/-- Finite local freeness of a fixed rank is invariant under an `R`-linear equivalence. -/
theorem iff_of_linearEquiv {N : Type w} [AddCommMonoid N] [Module R N] {r : ℕ}
    (e : M ≃ₗ[R] N) :
    FiniteLocallyFreeOfRank R M r ↔ FiniteLocallyFreeOfRank R N r := sorry

/-- The free rank-one module over a commutative semiring is finite locally free of rank one. -/
instance instSelf : FiniteLocallyFreeOfRank R R 1 :=
  sorry

end FiniteLocallyFreeOfRank

namespace FiniteLocallyFree

/-- Finite local freeness transports from the target of an `R`-linear equivalence to its source. -/
theorem of_linearEquiv {N : Type w} [AddCommMonoid N] [Module R N]
    (e : M ≃ₗ[R] N) (h : FiniteLocallyFree R N) :
    FiniteLocallyFree R M := sorry

/-- Finite local freeness is invariant under an `R`-linear equivalence. -/
theorem iff_of_linearEquiv {N : Type w} [AddCommMonoid N] [Module R N]
    (e : M ≃ₗ[R] N) :
    FiniteLocallyFree R M ↔ FiniteLocallyFree R N := sorry

/-- The regular module over a commutative semiring is finite locally free. -/
instance instSelf : FiniteLocallyFree R R :=
  sorry

end FiniteLocallyFree

end

end Module
