/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.CentralSimple.Centralizer.DoubleCentralizer
public import Mathlib.Tactic.CrossRefAttribute

/-! # Maximal Commutative Subalgebras and Subfields

The characterization of maximal commutative subalgebras via centralizers,
and the theory of maximal subfields of central division algebras.

## Main declarations

- `Subalgebra.IsMaximalCommutative` -- class for maximal commutative subalgebras
- `Subalgebra.centralizer_eq_iff_isMaximalCommutative` -- characterization via centralizer
- `Subalgebra.IsMaximalCommutative.centralizer_eq` -- a maximal commutative equals its centralizer
- `Subalgebra.IsMaximalCommutative.mem_of_commutes` -- membership criterion
- `Subalgebra.maximalCommutative_tfae` -- TFAE for subfields of CSAs
- `IsMaximalSubfield` -- class for maximal subfields of division algebras
- `IsMaximalSubfield.isField` -- a maximal subfield is indeed a field
- `IsMaximalSubfield.finrank_sq` -- the square-dimension formula

## References

- [Stacks Project, Tag 074V](https://stacks.math.columbia.edu/tag/074V)
- [Stacks Project, Tag 074W](https://stacks.math.columbia.edu/tag/074W)

@stack 074V
@stack 074W
-/

@[expose] public section

universe u v

namespace Subalgebra

section

variable {R : Type u} [CommSemiring R]
variable {A : Type v} [Semiring A] [Algebra R A]

/-- A subalgebra is maximal commutative if it is commutative and maximal among commutative
subalgebras. -/
class IsMaximalCommutative (K : Subalgebra R A) : Prop extends IsMulCommutative K where
  eq_of_le_of_comm (L : Subalgebra R A) (hKL : K ≤ L)
      (hcomm : ∀ x y : L, x * y = y * x) : L = K

theorem centralizer_eq_iff_isMaximalCommutative (K : Subalgebra R A) :
    centralizer R (K : Set A) = K ↔ K.IsMaximalCommutative := by
  constructor
  · intro hC
    refine
      { toIsMulCommutative := IsMulCommutative.of_comm fun x y ↦ ?_
        eq_of_le_of_comm := ?_ }
    · have hKC : K ≤ centralizer R (K : Set A) := hC.symm ▸ le_rfl
      exact Subtype.ext <| hKC y.2 x x.2
    · intro L hKL hcomm
      apply le_antisymm
      · intro x hx
        have hxC : x ∈ centralizer R (K : Set A) := by
          rw [mem_centralizer_iff]
          intro y hy
          exact congrArg Subtype.val (hcomm ⟨y, hKL hy⟩ ⟨x, hx⟩)
        simpa [hC] using hxC
      · exact hKL
  · intro hK
    letI : IsMulCommutative K := hK.toIsMulCommutative
    apply le_antisymm
    · intro x hxC
      rw [mem_centralizer_iff] at hxC
      have hcomm :
          ∀ a ∈ ((K : Set A) ∪ {x}), ∀ b ∈ ((K : Set A) ∪ {x}), a * b = b * a := by
        intro a ha b hb
        rcases ha with haK | rfl
        · rcases hb with hbK | rfl
          · exact setLike_mul_comm haK hbK
          · exact hxC a haK
        · rcases hb with hbK | rfl
          · exact (hxC b hbK).symm
          · simp
      let L : Subalgebra R A := Algebra.adjoin R ((K : Set A) ∪ {x})
      have hKL : K ≤ L := by
        intro y hy
        exact Algebra.subset_adjoin (Or.inl hy)
      letI : IsMulCommutative L := Algebra.isMulCommutative_adjoin R hcomm
      have hLK : L = K := hK.eq_of_le_of_comm L hKL fun a b ↦ by
        exact Subtype.ext <| setLike_mul_comm a.2 b.2
      have hxL : x ∈ L := by
        dsimp [L]
        exact Algebra.subset_adjoin (Or.inr (by simp))
      simpa [hLK] using hxL
    · have hKC : K ≤ centralizer R (K : Set A) := by
        intro x hx
        rw [mem_centralizer_iff]
        intro y hy
        exact setLike_mul_comm hy hx
      exact hKC

namespace IsMaximalCommutative

variable {K : Subalgebra R A}

theorem centralizer_eq (hK : K.IsMaximalCommutative) :
    centralizer R (K : Set A) = K :=
  (K.centralizer_eq_iff_isMaximalCommutative).2 hK

theorem mem_of_commutes (hK : K.IsMaximalCommutative) {x : A}
    (hx : ∀ y ∈ K, y * x = x * y) : x ∈ K := by
  have hxC : x ∈ centralizer R (K : Set A) := by
    rw [mem_centralizer_iff]
    intro y hy
    exact hx y hy
  simpa [hK.centralizer_eq] using hxC

end IsMaximalCommutative

end

end Subalgebra

section

open Subalgebra

variable {k : Type u} [Field k]
variable (A : CSA.{u, v} k)
variable (K : Subalgebra k A) (hK : IsField K)

local notation "C" => centralizer k (K : Set A)

private theorem subfield_le_centralizer (hK : IsField K) :
    K ≤ C := by
  letI : Field K := hK.toField
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  simpa using congrArg (fun z : K ↦ (z : A)) (mul_comm (⟨y, hy⟩ : K) ⟨x, hx⟩)

private theorem finrank_sq_iff_centralizer_eq (hK : IsField K) :
    Module.finrank k A = Module.finrank k K ^ 2 ↔ C = K := by
  letI : Field K := hK.toField
  have hKC : K ≤ C := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    simpa using mul_comm (⟨y, hy⟩ : K) ⟨x, hx⟩
  have hdim := K.finrank_centralizer A
  constructor
  · intro hsq
    have hfin : Module.finrank k K = Module.finrank k C := by
      exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos <| by
        calc
          Module.finrank k K * Module.finrank k K = Module.finrank k A := by
            simpa [pow_two] using hsq.symm
          _ = Module.finrank k K * Module.finrank k C := hdim
    exact (Subalgebra.eq_of_le_of_finrank_eq hKC hfin).symm
  · intro hC
    calc
      Module.finrank k A = Module.finrank k K * Module.finrank k C := hdim
      _ = Module.finrank k K ^ 2 := by rw [hC, pow_two]

-- Proof sketch: apply Theorem 11.7.1 to the field subalgebra `K`. The dimension formula
-- identifies condition (1) with `Module.finrank k (Subalgebra.centralizer k (K : Set A)) = 1`,
-- which is equivalent to the centralizer being `K`; condition (3) is equivalent to the same
-- centralizer statement because a commutative `k`-subalgebra containing `K` lies in that
-- centralizer, and conversely `K` itself is commutative since it is a field.
/-- For a subfield `K` of a finite central simple `k`-algebra `A`, represented as a
`k`-subalgebra with `IsField K`, the following are equivalent: `[A : k] = [K : k]^2`, `K` is its
own centralizer in `A`, and `K` is a maximal commutative `k`-subalgebra of `A`. -/
@[stacks 074V]
theorem maximalCommutative_tfae (hK : IsField K) :
    List.TFAE
      [ Module.finrank k A = Module.finrank k K ^ 2,
        C = K,
        K.IsMaximalCommutative ] := by
  letI : Field K := hK.toField
  tfae_have 1 ↔ 2 := finrank_sq_iff_centralizer_eq A K hK
  tfae_have 2 ↔ 3 := K.centralizer_eq_iff_isMaximalCommutative
  tfae_finish

end
section

open Subalgebra

variable {k : Type u} [Field k]
variable {A : Type v} [DivisionRing A] [Algebra k A] [FiniteDimensional k A]
  [Algebra.IsCentral k A]

/-- A `k`-subalgebra of a division algebra is a maximal subfield if it is commutative and maximal
among commutative `k`-subalgebras. In a division algebra, the field structure is then derived. -/
class IsMaximalSubfield (K : Subalgebra k A) : Prop extends K.IsMaximalCommutative

namespace IsMaximalSubfield

variable {K : Subalgebra k A}

omit [FiniteDimensional k A] [Algebra.IsCentral k A] in
theorem inv_mem (hK : IsMaximalSubfield K) {x : A} (hx : x ∈ K) : x⁻¹ ∈ K := by
  by_cases hx0 : x = 0
  · rw [hx0, inv_zero]
    exact K.zero_mem
  · refine hK.toIsMaximalCommutative.mem_of_commutes ?_
    intro y hy
    letI : IsMulCommutative K := hK.toIsMaximalCommutative.toIsMulCommutative
    have hxy : x * y = y * x := by
      exact setLike_mul_comm hx hy
    have hxy' : x⁻¹ * (x * y) * x⁻¹ = x⁻¹ * (y * x) * x⁻¹ :=
      congrArg (fun z : A ↦ x⁻¹ * z * x⁻¹) hxy
    calc
      y * x⁻¹ = (x⁻¹ * x) * y * x⁻¹ := by rw [inv_mul_cancel₀ hx0, one_mul]
      _ = x⁻¹ * (x * y) * x⁻¹ := by simp [mul_assoc]
      _ = x⁻¹ * (y * x) * x⁻¹ := hxy'
      _ = x⁻¹ * y * (x * x⁻¹) := by simp [mul_assoc]
      _ = x⁻¹ * y := by rw [mul_inv_cancel₀ hx0, mul_one]

omit [FiniteDimensional k A] [Algebra.IsCentral k A] in
theorem isField (hK : IsMaximalSubfield K) : IsField K := by
  letI : IsMulCommutative K := hK.toIsMaximalCommutative.toIsMulCommutative
  refine ⟨⟨0, 1, zero_ne_one⟩, fun a b ↦ Subtype.ext <| setLike_mul_comm a.2 b.2, ?_⟩
  intro a ha
  refine ⟨⟨(a : A)⁻¹, hK.inv_mem a.2⟩, ?_⟩
  apply Subtype.ext
  exact mul_inv_cancel₀ fun h ↦ ha <| Subtype.ext h

-- attribute [instance] isField -- IsField is not a typeclass

noncomputable instance (K : Subalgebra k A) [hK : IsMaximalSubfield K] : Field K :=
  hK.isField.toField

-- Proof sketch: apply Lemma 11.7.3 to the subfield `K ⊆ A`, using the derived field structure on
-- `K`. The maximal-subfield hypothesis yields the maximal-commutative clause of the TFAE, so the
-- implication from (3) to (1) gives the square-dimension formula.
/-- If `A` is a finite central skew field over `k` and `K` is a maximal subfield of
`A`, encoded by `IsMaximalSubfield K`, then `[A : k] = [K : k]^2`. -/
@[stacks 074W]
theorem finrank_sq (K : Subalgebra k A) [hK : IsMaximalSubfield K] :
    Module.finrank k A = Module.finrank k K ^ 2 := by
  let A' : CSA.{u, v} k := CSA.mk (AlgCat.of k A)
  exact
    ((maximalCommutative_tfae A' K hK.isField).out 2 0).mp
      hK.toIsMaximalCommutative

end IsMaximalSubfield

end

end
