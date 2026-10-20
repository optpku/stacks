module

public import ReasLib.RingTheory.RestrictedPowerSeries.Regular
import StacksCheckRecall

/-!
# Regularity of restricted power series after quotient by a rig-closed prime
-/

@[expose] public section

universe u

open scoped TensorProduct

/- Lemma 88.14.12 (1): if `A` is an adic Noetherian topological ring and `p ⊂ A`
is a rig-closed prime, then for every `n ≥ 1` the ring map
`A ⧸ p →+* RestrictedPowerSeries (Fin n) A ⊗[A] (A ⧸ p)`, identified in the
source with `A ⧸ p → (A ⧸ p){x₁, …, xₙ}`, is regular. -/
@[stacks 0GGJ] #check (RestrictedPowerSeries.tensorQuotientHom_regular :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
    (n : ℕ) [NeZero n] (p : Ideal A) [p.IsRigClosed],
    ((Algebra.TensorProduct.includeRight :
      (A ⧸ p) →ₐ[A] RestrictedPowerSeries (Fin n) A ⊗[A] (A ⧸ p)).toRingHom).Regular)

/- Lemma 88.14.12 (2): in particular, `p.Fiber (RestrictedPowerSeries (Fin n) A)`,
the algebra `κ(p) ⊗[A] RestrictedPowerSeries (Fin n) A` identified in the source
with `RestrictedPowerSeries (Fin n) A ⊗[A] κ(p)` up to `TensorProduct.comm`, is
geometrically regular over `κ(p)`. -/
@[stacks 0GGJ] #check (RestrictedPowerSeries.fiber_isGeometricallyRegular :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]
    (n : ℕ) [NeZero n] (p : Ideal A) [p.IsRigClosed],
    Algebra.IsGeometricallyRegular p.ResidueField
      (p.Fiber (RestrictedPowerSeries (Fin n) A)))
