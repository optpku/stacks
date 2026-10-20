/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Submodule.Filtration
import StacksCheckRecall

/-!
# Lemma 12.23.5: Submodule Representatives

The linear-algebraic representative inequalities are owned by the filtered-linear-map API.
-/

@[expose] public section

universe uR uM uN

variable {R : Type uR} [Semiring R]
variable {M : Type uM} [AddCommMonoid M] [Module R M]
variable {N : Type uN} [AddCommMonoid N] [Module R N]
variable (d : M →ₗ[R] N) (F : ℤ → Submodule R M)
  (G : ℤ → Submodule R N) (p : ℤ)

/- Equation 12.23.5.2 [012F]: eventual boundary representatives are contained in the intrinsic
range representative. -/
@[stacks 012F]
#check (Submodule.FilteredLinearMap.Representative.Boundary.eventual_le_range
  d F G p :
    Submodule.FilteredLinearMap.eventualBoundaryRepresentative d F G p ≤
      Submodule.FilteredLinearMap.rangeRepresentative d G p)

/- The dual cycle-side inequality is part of the same reusable representative API. -/
#check (Submodule.FilteredLinearMap.Representative.Cycle.kernel_le_eventual
  d F G p :
    Submodule.FilteredLinearMap.kernelRepresentative d F p ≤
      Submodule.FilteredLinearMap.eventualCycleRepresentative d F G p)
