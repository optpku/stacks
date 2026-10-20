module

import StacksCheckRecall
import ReasLib.RingTheory.CompleteIntersection.OverField.Smoothing

universe u v

open scoped TensorProduct

/- Lemma 93.17.4 -/
@[stacks 0E7W] #check
  (IsLocalCompleteIntersection.exists_flat_finite_etale_smoothing :
    ∀ {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
      [FiniteDimensional k A] [IsLocalCompleteIntersection k A],
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra (PowerSeries k) B)
      (_ : Algebra k B) (_ : IsScalarTower k (PowerSeries k) B)
      (_ : Module.Flat (PowerSeries k) B) (_ : Module.Finite (PowerSeries k) B)
      (_ : (B ⧸ Ideal.span {(algebraMap (PowerSeries k) B) (PowerSeries.X : PowerSeries k)}) ≃ₐ[k] A),
      Algebra.Etale (LaurentSeries k) (LaurentSeries k ⊗[PowerSeries k] B))
