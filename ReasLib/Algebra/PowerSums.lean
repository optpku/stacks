module

public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v

namespace PowerSums

/-- Lemma 9.13.2 (Tag 0EM9): for a nonempty finite family of distinct elements of a commutative
domain, some power sum is nonzero. -/
theorem existsExponentSumNeZero
    {L : Type u} [CommRing L] [IsDomain L] {ι : Type v} [Fintype ι] [Nonempty ι]
    (α : ι → L) (hα : Function.Injective α) :
    ∃ e : ℕ, ∑ i, α i ^ e ≠ 0 := by
  let χ : ι → Multiplicative ℕ →* L := powersHom L ∘ α
  have hχ_base :=
    (linearIndependent_monoidHom (Multiplicative ℕ) L).comp χ
      (by simpa [χ] using ((powersHom L).injective.comp hα))
  have hχ : LinearIndependent L fun i ↦ (χ i : Multiplicative ℕ → L) := by
    convert hχ_base using 1
    ext i e
    rfl
  have hsum_ne : ∑ i, (1 : L) • (χ i : Multiplicative ℕ → L) ≠ 0 := by
    intro hsum
    have hone := (Fintype.linearIndependent_iff.mp hχ) (fun _ ↦ (1 : L)) hsum
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact one_ne_zero (hone i)
  by_contra h
  apply hsum_ne
  ext e
  simpa [χ] using (not_exists.mp h e.toAdd)

end PowerSums
