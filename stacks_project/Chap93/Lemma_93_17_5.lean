module

import StacksCheckRecall
import ReasLib.RingTheory.CompleteIntersection.OverField.Smoothing

universe u v

/- Lemma 93.17.5 -/
@[stacks 0E7X] #check
  (Algebra.IsCompleteIntersectionOver.exists_flat_essFiniteType_fitting :
    ∀ {k : Type u} [Field k] {A : Type v}
      [CommRing A] [Algebra k A] [IsLocalRing A] [Algebra.EssFiniteType k A]
      [Algebra.IsCompleteIntersectionOver k A] (d : ℕ)
      (hd : ringKrullDim A +
          (Cardinal.toNat (Algebra.trdeg k (IsLocalRing.ResidueField A)) : WithBot ℕ∞) = d),
    ∃ (B : Type (max u v)) (_ : CommRing B) (_ : Algebra (PowerSeries k) B)
      (_ : Algebra k B) (_ : IsScalarTower k (PowerSeries k) B)
      (_ : Module.Flat (PowerSeries k) B) (_ : Algebra.EssFiniteType (PowerSeries k) B)
      (e : (B ⧸ Ideal.span {(algebraMap (PowerSeries k) B) (PowerSeries.X : PowerSeries k)}) ≃ₐ[k] A)
      (n : ℕ),
      algebraMap (PowerSeries k) B (PowerSeries.X ^ n) ∈
        fittingIdeal B (KaehlerDifferential (PowerSeries k) B) d)
