/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Subring.Basic

@[expose] public section

universe u

namespace Multicross

/-- The subring of `n`-tuples of power series whose constant coefficients all agree. -/
noncomputable def ring (k : Type u) [Field k] (n : ℕ) : Subring (Fin n → PowerSeries k) :=
  ⨅ first : Fin n, ⨅ second : Fin n,
    RingHom.eqLocus
      (PowerSeries.constantCoeff.comp (Pi.evalRingHom (fun _ : Fin n ↦ PowerSeries k) first))
      (PowerSeries.constantCoeff.comp (Pi.evalRingHom (fun _ : Fin n ↦ PowerSeries k) second))

/-- Membership in `Multicross.ring k n` means that every pair of constant coefficients agrees. -/
@[simp]
theorem mem_ring {k : Type u} [Field k] {n : ℕ} {f : Fin n → PowerSeries k} :
    f ∈ ring k n ↔
      ∀ i j, PowerSeries.constantCoeff (f i) = PowerSeries.constantCoeff (f j) := sorry

/-- Constant power-series tuples belong to the multicross ring. -/
theorem algebraMap_mem {k : Type u} [Field k] {n : ℕ} (c : k) :
    algebraMap k (Fin n → PowerSeries k) c ∈ ring k n := sorry

/-- The canonical `k`-algebra structure on the multicross ring, induced by diagonal
constant power-series tuples. -/
noncomputable instance instAlgebra {k : Type u} [Field k] {n : ℕ} : Algebra k (ring k n) :=
  RingHom.toAlgebra <|
    (algebraMap k (Fin n → PowerSeries k)).codRestrict (ring k n)
      (fun c ↦ algebraMap_mem c)

/-- The `i`-th coordinate of a scalar in the multicross ring is its constant power series. -/
@[simp]
theorem algebraMap_apply {k : Type u} [Field k] {n : ℕ} (c : k) (i : Fin n) :
    (algebraMap k (ring k n) c : Fin n → PowerSeries k) i = PowerSeries.C c := sorry

end Multicross
