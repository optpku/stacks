module

public import ReasLib.RingTheory.Normalization.OneDimensional.Branches
import StacksCheckRecall

@[expose] public section

open IsLocalRing

universe u v w

/- Lemma 53.16.1 (1): the normalization delta invariant of a one-dimensional reduced
Nagata local `k`-algebra with residue field `k` is at least its branch number minus one. -/
@[stacks 0C1V] #check (Normalization.OneDimensional.deltaInvariant_ge_branchNumber_sub_one :
  ∀ {k : Type u} [Field k] [IsSepClosed k]
    {A : Type v} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A] [Algebra k A]
    {Ah : Type w} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah],
    Function.Bijective (ResidueField.map (algebraMap k A)) → ringKrullDim A = 1 →
      Normalization.deltaInvariant A ≥ branchNumber A Ah - 1)

/- Lemma 53.16.1 (2): equality in the branch bound identifies the maximal-ideal
completion with the multicross ring having the same number of branches. -/
@[stacks 0C1V] #check
  (Normalization.OneDimensional.exists_completion_algEquiv_multicross_of_deltaInvariant_eq :
    ∀ {k : Type u} [Field k] [IsSepClosed k]
      {A : Type v} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A] [Algebra k A]
      {Ah : Type w} [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah],
      Function.Bijective (ResidueField.map (algebraMap k A)) → ringKrullDim A = 1 →
      Normalization.deltaInvariant A = branchNumber A Ah - 1 →
        ∃ n : ℕ, branchNumber A Ah = (n : ℕ∞) ∧
          Nonempty (AdicCompletion (maximalIdeal A) A ≃ₐ[k] Multicross.ring k n))
