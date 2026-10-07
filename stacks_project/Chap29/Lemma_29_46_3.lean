module

import StacksCheckRecall
import ReasLib.RingTheory.Localization.Integer

universe u

/- Lemma 29.46.3: an element outside the base localization whose prescribed
coefficient-weighted powers lie in the base localization admits a numerator outside the base ring
for which those powers lie in the base ring. -/
@[stacks 0CN9] #check
  (IsLocalization.exists_numerator_not_isInteger_of_mul_pow_isInteger :
    ∀ {A B Aₛ Bₛ : Type u} [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₛ]
      [Algebra A B] [FaithfulSMul A B] {S : Submonoid A}
      [Algebra A Aₛ] [IsLocalization S Aₛ]
      [Algebra B Bₛ] [IsLocalization (Algebra.algebraMapSubmonoid B S) Bₛ]
      [Algebra A Bₛ] [Algebra Aₛ Bₛ]
      [IsScalarTower A B Bₛ] [IsScalarTower A Aₛ Bₛ]
      {n : ℕ} (hn : 0 < n) (b : Fin n → B) (x : Bₛ)
      (hx : ¬ IsLocalization.IsInteger Aₛ x)
      (hbx : ∀ i,
        IsLocalization.IsInteger Aₛ
          (algebraMap B Bₛ (b i) * x ^ ((i : ℕ) + 1))),
      ∃ (s : S) (y : B),
        algebraMap B Bₛ y = algebraMap A Bₛ s * x ∧
          ¬ IsLocalization.IsInteger A y ∧
            ∀ i, IsLocalization.IsInteger A (b i * y ^ ((i : ℕ) + 1)))
