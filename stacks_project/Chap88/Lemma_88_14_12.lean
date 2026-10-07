module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.GeometricRegularity
public import ReasLib.RingTheory.Regular.RingMap
public import stacks_project.Chap87.Remark_87_28_1_Universal_property_restricted_power_series_RestrictedPowerSeries
public import stacks_project.Chap88.Lemma_88_14_3_RigClosed

/-!
# Regularity of restricted power series after quotient by a rig-closed prime
-/

@[expose] public section

universe u

open scoped TensorProduct
open Algebra.TensorProduct

noncomputable section

namespace RestrictedPowerSeries

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/-- The canonical ring map `A ⧸ p →+* RestrictedPowerSeries (Fin n) A ⊗[A] (A ⧸ p)`,
identified in the source with `A ⧸ p → (A ⧸ p){x₁, …, xₙ}`. -/
def tensorQuotientHom (n : ℕ) (p : Ideal A) :
    (A ⧸ p) →+* RestrictedPowerSeries (Fin n) A ⊗[A] (A ⧸ p) :=
  includeRight.toRingHom

/-- The canonical quotient tensor map sends `a` to `1 ⊗ₜ a`. -/
theorem tensorQuotientHom_apply (n : ℕ) (p : Ideal A) (a : A ⧸ p) :
    tensorQuotientHom n p a = 1 ⊗ₜ a :=
  sorry

/-- Lemma 88.14.12 (1): if `A` is an adic Noetherian topological ring and `p ⊂ A`
is a rig-closed prime, then for every `n ≥ 1` the ring map
`A ⧸ p →+* RestrictedPowerSeries (Fin n) A ⊗[A] (A ⧸ p)`, identified in the
source with `A ⧸ p → (A ⧸ p){x₁, …, xₙ}`, is regular. -/
@[stacks 0GGJ]
instance tensorQuotientHom_regular (n : ℕ) [NeZero n] (p : Ideal A) [p.IsRigClosed] :
    (tensorQuotientHom n p).Regular :=
  sorry

/-- Lemma 88.14.12 (2): in particular, `p.Fiber (RestrictedPowerSeries (Fin n) A)`,
the algebra `κ(p) ⊗[A] RestrictedPowerSeries (Fin n) A` identified in the source
with `RestrictedPowerSeries (Fin n) A ⊗[A] κ(p)` up to `TensorProduct.comm`, is
geometrically regular over `κ(p)`. -/
@[stacks 0GGJ]
instance fiber_isGeometricallyRegular (n : ℕ) [NeZero n] (p : Ideal A)
    [p.IsRigClosed] :
    Algebra.IsGeometricallyRegular p.ResidueField
      (p.Fiber (RestrictedPowerSeries (Fin n) A)) :=
  sorry

end RestrictedPowerSeries
