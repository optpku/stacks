module

import StacksCheckRecall
import ReasLib.RingTheory.Sequence.Koszul.Regularity.BaseChange

noncomputable section

universe u

open scoped TensorProduct

/- Remark 31.22.5: a quasi-regular family with flat quotient stays quasi-regular after base
change; if the ambient algebra is flat and finitely presented, then its image is regular after
localization at every prime containing the generated ideal. -/
@[stacks 0FUD] #check
  (RingTheory.Sequence.IsQuasiRegularSequence.isRegular_localizationAtPrime_baseChange :
    ∀ {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
      [Algebra A B] [Algebra A A'] {n : ℕ} (f : Fin n → B)
      [Module.Flat A B] [Algebra.FinitePresentation A B]
      [Module.Flat A (B ⧸ Ideal.span (Set.range f))],
      RingTheory.Sequence.IsQuasiRegularSequence (List.ofFn f) →
      ∀ q' : PrimeSpectrum (A' ⊗[A] B),
        Ideal.span
          (Set.range (fun i ↦
            (Algebra.TensorProduct.includeRight (f i) : A' ⊗[A] B))) ≤ q'.asIdeal →
        RingTheory.Sequence.IsRegular (Localization.AtPrime q'.asIdeal)
          (List.ofFn fun i ↦
            algebraMap (A' ⊗[A] B) (Localization.AtPrime q'.asIdeal)
              (Algebra.TensorProduct.includeRight (f i))))

#check
  (RingTheory.Sequence.IsQuasiRegularSequence.baseChange_of_flat_quotient :
    ∀ {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
      [Algebra A B] [Algebra A A'] {n : ℕ} (f : Fin n → B)
      [Module.Flat A (B ⧸ Ideal.span (Set.range f))],
      RingTheory.Sequence.IsQuasiRegularSequence (List.ofFn f) →
        RingTheory.Sequence.IsQuasiRegularSequence
          (List.ofFn fun i ↦
            (Algebra.TensorProduct.includeRight (f i) : A' ⊗[A] B)))

end
