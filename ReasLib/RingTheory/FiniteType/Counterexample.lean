module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

namespace Algebra.FiniteType

/-- There exists a local ring `A`, a finite type `A`-algebra `B`, and a prime ideal `q`
lying over the maximal ideal of `A` such that `Localization.AtPrime q` is flat over `A`,
while every principal localization `Localization.Away g` with `g ∉ q` is neither of
finite presentation nor flat over `A`. -/
@[stacks 05G2]
theorem exists_flat_atPrime_not_flat_away :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (_ : Algebra A B)
      (_ : IsLocalRing A) (q : Ideal B) (_ : q.IsPrime),
      Algebra.FiniteType A B ∧
        Ideal.comap (algebraMap A B) q = IsLocalRing.maximalIdeal A ∧
        Module.Flat A (Localization.AtPrime q) ∧
        ∀ g : B, g ∉ q →
          ¬ Algebra.FinitePresentation A (Localization.Away g) ∧
            ¬ Module.Flat A (Localization.Away g) := sorry

end Algebra.FiniteType
