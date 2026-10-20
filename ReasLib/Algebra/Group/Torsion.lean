module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

@[expose] public section

universe u

open AddMonoid AddSubgroup

namespace AddCommGroup

section

variable {A : Type u} [AddCommGroup A] {n : ℕ}

/-- The `gcd`-torsion subgroup inherits the cardinality bound for divisors of `n`. -/
private theorem natCardTorsionByGcdLe [Finite A]
    (hcard : ∀ d : ℕ, d ∣ n → Cardinal.mk A[d] ≤ d) (d : ℕ) :
    Nat.card A[d.gcd n] ≤ d.gcd n := by
  have := Cardinal.toNat_le_toNat
    (hcard (d.gcd n) (Nat.gcd_dvd_right d n)) Cardinal.natCast_lt_aleph0
  simpa [Nat.card] using this

/-- The elements killed by `d` satisfy the cardinality bound inherited from the
`gcd d n`-torsion subgroup. -/
private theorem natCardNsmulEqZeroLeOfTorsionCardinalLe [Finite A]
    (hexp : exponent A ∣ n)
    (hcard : ∀ d : ℕ, d ∣ n → Cardinal.mk A[d] ≤ d) :
    ∀ d : ℕ, 0 < d → Nat.card {a : A // d • a = 0} ≤ d := by
  intro d hd
  let f : {a : A // d • a = 0} → A[d.gcd n] := fun a ↦
    ⟨a.1, torsionBy.nsmul_iff.mpr (gcd_nsmul_eq_zero.2
      ⟨a.2, (exponent_dvd_iff_forall_nsmul_eq_zero.mp hexp) a.1⟩)⟩
  calc
    Nat.card {a : A // d • a = 0} ≤ Nat.card A[d.gcd n] :=
      Nat.card_le_card_of_injective f fun a b hab ↦
        Subtype.ext (congrArg (fun x : A[d.gcd n] ↦ x.1) hab)
    _ ≤ d.gcd n := natCardTorsionByGcdLe hcard d
    _ ≤ d := Nat.gcd_le_left n hd

/-- A bounded cardinality condition on torsion subgroups of an abelian group forces the group to
be finite. -/
theorem finiteOfTorsionCardinalLe (hexp : exponent A ∣ n)
    (hcard : ∀ d : ℕ, d ∣ n → Cardinal.mk A[d] ≤ d) :
    Finite A := by
  have hfiniteTorsion : Finite ↥A[n] := by
    refine Cardinal.lt_aleph0_iff_finite.mp ?_
    exact lt_of_le_of_lt (hcard n dvd_rfl) Cardinal.natCast_lt_aleph0
  -- Local instance justification (proof-local temporary data): use finiteness of the `n`-torsion subgroup as the codomain of the embedding.
  letI : Finite ↥A[n] := hfiniteTorsion
  refine Finite.of_injective
      (fun x : A ↦ (⟨x, torsionBy.nsmul_iff.mpr
        ((exponent_dvd_iff_forall_nsmul_eq_zero.mp hexp) x)⟩ : A[n])) ?_
  intro x y hxy
  simpa using hxy

/-- A bounded cardinality condition on torsion subgroups of an abelian group forces it to be
cyclic. -/
theorem isAddCyclicOfTorsionCardinalLe (hexp : exponent A ∣ n)
    (hcard : ∀ d : ℕ, d ∣ n → Cardinal.mk A[d] ≤ d) :
    IsAddCyclic A := by
  -- Local instance justification (proof-local temporary data): derive finiteness from the torsion-cardinality hypothesis.
  letI : Finite A := finiteOfTorsionCardinalLe hexp hcard
  classical
  -- Local instance justification (proof-local temporary data): choose a finite enumeration for the canonical cyclicity criterion.
  letI : Fintype A := Fintype.ofFinite A
  exact isAddCyclic_of_card_nsmul_eq_zero_le fun d hd ↦ by
    simpa [Fintype.card_subtype, Nat.card_eq_fintype_card] using
      natCardNsmulEqZeroLeOfTorsionCardinalLe hexp hcard d hd

/-- Under the bounded torsion-cardinality condition, the finite cardinality of an abelian group
divides its exponent bound. -/
theorem natCardDvdOfTorsionCardinalLe (hexp : exponent A ∣ n)
    (hcard : ∀ d : ℕ, d ∣ n → Cardinal.mk A[d] ≤ d) :
    Nat.card A ∣ n := by
  -- Local instance justification (proof-local temporary data): derive finiteness before comparing the exponent with the cardinality.
  letI : Finite A := finiteOfTorsionCardinalLe hexp hcard
  -- Local instance justification (proof-local temporary data): invoke the cyclicity consequence of the same cardinality bound.
  letI : IsAddCyclic A := isAddCyclicOfTorsionCardinalLe hexp hcard
  rw [← IsAddCyclic.exponent_eq_card]
  exact hexp

/-- Lemma 9.17.1 (Tag 09HX): if an abelian group of exponent dividing `n` has exactly `d`
elements in its `d`-torsion subgroup for every divisor `d` of `n`, then it is cyclic. -/
theorem isAddCyclicOfTorsionCardinalEq (hexp : exponent A ∣ n)
    (hcard : ∀ d : ℕ, d ∣ n → Cardinal.mk A[d] = d) :
    IsAddCyclic A :=
  isAddCyclicOfTorsionCardinalLe hexp fun d hd ↦ by
    simpa [torsionBy.nsmul_iff] using (le_of_eq (hcard d hd) : Cardinal.mk A[d] ≤ d)

end

end AddCommGroup
