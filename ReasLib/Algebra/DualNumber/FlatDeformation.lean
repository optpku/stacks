/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.RingHom.Flat

@[expose] public section

noncomputable section

universe u

open TrivSqZeroExt
open scoped DualNumber

namespace DualNumber

/-- The canonical `k`-algebra map `DualNumber k → DualNumber A` sending `ε` to `ε`,
induced by `algebraMap k A`. -/
def algebraMapOfAlgebra (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] :
    DualNumber k →ₐ[k] DualNumber A :=
  lift ⟨(Algebra.ofId k (DualNumber A), (eps : DualNumber A)),
    eps_mul_eps, fun _ ↦ commute_eps_left _⟩

/-- `algebraMapOfAlgebra k A` sends `ε` in `DualNumber k` to `ε` in `DualNumber A`. -/
theorem algebraMapOfAlgebra_eps (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] :
    algebraMapOfAlgebra k A eps = (eps : DualNumber A) := sorry

/-- `algebraMapOfAlgebra k A` extends `algebraMap k A` on constant terms. -/
theorem algebraMapOfAlgebra_inl (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    (x : k) :
    algebraMapOfAlgebra k A (inl x) = inl (algebraMap k A x) := sorry

/-- The special fibre `DualNumber A ⧸ (ε)` of the trivial dual-number extension. -/
abbrev quotEps (A : Type u) [CommRing A] : Type u :=
  DualNumber A ⧸ Ideal.span {(eps : DualNumber A)}

/-- For a field `k` and a `k`-algebra `A`, the map `algebraMapOfAlgebra k A` is flat,
and its special fibre `DualNumber A ⧸ (ε)` is isomorphic to `A` as a `k`-algebra. -/
theorem algebraMapOfAlgebra_flat_specialFiber
    (k A : Type u) [Field k] [CommRing A] [Algebra k A] :
    (algebraMapOfAlgebra k A).toRingHom.Flat ∧
      Nonempty (quotEps A ≃ₐ[k] A) := sorry

end DualNumber
