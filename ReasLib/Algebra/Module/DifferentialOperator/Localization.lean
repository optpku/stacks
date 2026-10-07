module

public import ReasLib.Algebra.Module.DifferentialOperator.FormallyEtale
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of Differential Operators

This leaf owns the localization form of scalar extension for bounded
differential operators.  It is a direct consumer interface for the generic
formally-etale base-change theorem, without exposing a tensor-product
presentation to callers.

@stack 0G36
-/

@[expose] public section

universe u

namespace LinearMap.IsDifferentialOperatorOfOrder.Localization

section Localization

variable {R S M N : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable (T : Submonoid S)
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- An operator on localized modules is an extension of `D` of order `k` when it commutes with
the canonical localization maps and has the same order bound. -/
@[stacks 0G36]
def IsExtension (D : M →ₗ[R] N) (k : ℕ)
    (D' : LocalizedModule T M →ₗ[R] LocalizedModule T N) : Prop :=
  D'.comp ((LocalizedModule.mkLinearMap T M).restrictScalars R) =
      ((LocalizedModule.mkLinearMap T N).restrictScalars R).comp D ∧
    D'.IsDifferentialOperatorOfOrder (Localization T) k

/-- A differential operator of order at most `k` has a unique order-preserving extension to
localization at `T`. -/
@[stacks 0G36]
theorem existsUnique_extension {D : M →ₗ[R] N} {k : ℕ}
    (hD : D.IsDifferentialOperatorOfOrder S k) :
    ∃! D' : LocalizedModule T M →ₗ[R] LocalizedModule T N, IsExtension T D k D' := sorry

end Localization

end LinearMap.IsDifferentialOperatorOfOrder.Localization
