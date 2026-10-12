/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Order.Filtration

/-!
# Filtration Representatives for Linear Maps

This file records the submodule representatives that occur in the spectral sequence of a
filtered differential module.  The definitions are made for a linear map between two filtered
modules; the differential-object criteria are the endomorphism specialization.
-/

@[expose] public section

universe uR uM uN

namespace Submodule.FilteredLinearMap

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {N : Type uN} [AddCommMonoid N] [Module R N]

/-- The page-`r` cycle representative at filtration index `p`. -/
@[stacks 012F "cycle representative of a filtered linear map"]
def cycleRepresentative (d : M →ₗ[R] N) (F : ℤ → Submodule R M)
    (G : ℤ → Submodule R N) (r : ℕ) (p : ℤ) : Submodule R M :=
  (F p ⊓ Submodule.comap d (G (p + r))) ⊔ F (p + 1)

/-- The page-`r` boundary representative at filtration index `p`. -/
@[stacks 012F "boundary representative of a filtered linear map"]
def boundaryRepresentative (d : M →ₗ[R] N) (F : ℤ → Submodule R M)
    (G : ℤ → Submodule R N) (r : ℕ) (p : ℤ) : Submodule R N :=
  (G p ⊓ Submodule.map d (F (p - r + 1))) ⊔ G (p + 1)

/-- The intrinsic cycle representative `(LinearMap.ker d ⊓ F p) ⊔ F (p + 1)`. -/
@[stacks 012F "intrinsic cycle representative of a filtered linear map"]
def kernelRepresentative (d : M →ₗ[R] N) (F : ℤ → Submodule R M)
    (p : ℤ) : Submodule R M :=
  (LinearMap.ker d ⊓ F p) ⊔ F (p + 1)

/-- The intrinsic boundary representative `(LinearMap.range d ⊓ G p) ⊔ G (p + 1)`. -/
@[stacks 012F "intrinsic boundary representative of a filtered linear map"]
def rangeRepresentative (d : M →ₗ[R] N) (G : ℤ → Submodule R N)
    (p : ℤ) : Submodule R N :=
  (LinearMap.range d ⊓ G p) ⊔ G (p + 1)

/-- The eventual cycle representative, obtained by intersecting the finite-page stages. -/
@[stacks 012F "eventual cycle representative of a filtered linear map"]
noncomputable abbrev eventualCycleRepresentative (d : M →ₗ[R] N)
    (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) (p : ℤ) : Submodule R M :=
  ⨅ r : ℕ, cycleRepresentative d F G r p

/-- The eventual boundary representative, obtained by taking the union of the finite-page
stages. -/
@[stacks 012F "eventual boundary representative of a filtered linear map"]
noncomputable abbrev eventualBoundaryRepresentative (d : M →ₗ[R] N)
    (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) (p : ℤ) : Submodule R N :=
  ⨆ r : ℕ, boundaryRepresentative d F G r p

namespace Representative

namespace Cycle

/-- Intrinsic cycles lie in every eventual cycle stage. -/
@[stacks 012F "intrinsic cycles lie in the eventual cycle representative"]
theorem kernel_le_eventual
    (d : M →ₗ[R] N) (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) (p : ℤ) :
    kernelRepresentative d F p ≤ eventualCycleRepresentative d F G p := sorry

end Cycle

namespace Boundary

/-- Eventual boundaries lie in the intrinsic boundary stage. -/
@[stacks 012F "eventual boundaries lie in the intrinsic boundary representative"]
theorem eventual_le_range
    (d : M →ₗ[R] N) (F : ℤ → Submodule R M) (G : ℤ → Submodule R N) (p : ℤ) :
    eventualBoundaryRepresentative d F G p ≤ rangeRepresentative d G p := sorry

end Boundary

end Representative

section Endomorphism

variable {M : Type uM} [AddCommMonoid M] [Module R M]

/-- The representative criterion for weak convergence of a filtered linear endomorphism. -/
@[stacks 012J "weak convergence criterion for a filtered differential module"]
def weakConvergenceCriterion (d : M →ₗ[R] M) (F : ℤ → Submodule R M) : Prop :=
  ∀ p : ℤ,
    eventualBoundaryRepresentative d F F p = rangeRepresentative d F p ∧
      kernelRepresentative d F p = eventualCycleRepresentative d F F p

namespace WeakConvergence

/-- Extract the eventual-boundary equality in one filtration degree. -/
theorem eventualBoundary_eq {d : M →ₗ[R] M} {F : ℤ → Submodule R M}
    (h : weakConvergenceCriterion d F) (p : ℤ) :
    eventualBoundaryRepresentative d F F p = rangeRepresentative d F p := sorry

/-- Extract the eventual-cycle equality in one filtration degree. -/
theorem kernel_eq_eventualCycle {d : M →ₗ[R] M} {F : ℤ → Submodule R M}
    (h : weakConvergenceCriterion d F) (p : ℤ) :
    kernelRepresentative d F p = eventualCycleRepresentative d F F p := sorry

/-- Build weak convergence from the two pointwise representative equalities. -/
theorem of_equalities {d : M →ₗ[R] M} {F : ℤ → Submodule R M}
    (hB : ∀ p : ℤ,
      eventualBoundaryRepresentative d F F p = rangeRepresentative d F p)
    (hZ : ∀ p : ℤ,
      kernelRepresentative d F p = eventualCycleRepresentative d F F p) :
    weakConvergenceCriterion d F := sorry

end WeakConvergence

/-- The representative of the `p`-th stage of the filtration induced on cohomology. -/
@[stacks 012J "induced cohomology filtration representative of a filtered linear map"]
def cohomologyFiltrationRepresentative (d : M →ₗ[R] M)
    (F : ℤ → Submodule R M) (p : ℤ) : Submodule R M :=
  Order.Filtration.Subquotient.representative F (LinearMap.range d) (LinearMap.ker d) p

end Endomorphism

end Submodule.FilteredLinearMap
