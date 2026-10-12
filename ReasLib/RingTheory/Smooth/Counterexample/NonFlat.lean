/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.Smooth

@[expose] public section

universe u

namespace AddMonoidAlgebra

/-- The augmentation `AddMonoidAlgebra k ℚ →+* k` sending each basis element `single α c`
to the scalar `c`, hence sending `single α 1` to `1`. -/
noncomputable def ratAugmentation (k : Type u) [CommRing k] :
    AddMonoidAlgebra k ℚ →+* k :=
  (lift k k ℚ (1 : Multiplicative ℚ →* k)).toRingHom

/-- Evaluating the rational group-algebra augmentation at a basis element `single α c`
returns the scalar `c`. -/
theorem ratAugmentation_single {k : Type u} [CommRing k] (α : ℚ) (c : k) :
    ratAugmentation k (single α c) = c := sorry

/-- Over a field of positive characteristic, the rational group-algebra augmentation is
formally smooth. -/
theorem ratAugmentation_formallySmooth {k : Type u} [Field k] {p : ℕ} [Fact p.Prime]
    [CharP k p] : (ratAugmentation k).FormallySmooth := sorry

/-- The rational group-algebra augmentation is not flat: it sends the nonzerodivisor
`single 2 1 - 1` to `0`. -/
theorem ratAugmentation_not_flat {k : Type u} [Field k] :
    ¬ (ratAugmentation k).Flat := sorry

end AddMonoidAlgebra

namespace RingHom

/-- There exists a formally smooth ring map which is not flat. -/
theorem exists_formallySmooth_not_flat :
    ∃ (R S : Type u) (_ : CommRing R) (_ : CommRing S) (f : R →+* S),
      f.FormallySmooth ∧ ¬ f.Flat := sorry

end RingHom
