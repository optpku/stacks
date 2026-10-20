module

import StacksCheckRecall
import ReasLib.RingTheory.CompleteIntersection.OverField.Smoothing

universe u v

open scoped TensorProduct

/- Lemma 93.17.3 -/
@[stacks 0E7V] #check
  (IsGlobalCompleteIntersection.exists_flat_finiteType_smoothing :
    ∀ {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
      [IsGlobalCompleteIntersection k A],
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra (PowerSeries k) B)
      (_ : Algebra k B) (_ : IsScalarTower k (PowerSeries k) B)
      (_ : Module.Flat (PowerSeries k) B) (_ : Algebra.FiniteType (PowerSeries k) B)
      (_ : (B ⧸ Ideal.span {(algebraMap (PowerSeries k) B) (PowerSeries.X : PowerSeries k)}) ≃ₐ[k] A),
      Algebra.Smooth (LaurentSeries k) (LaurentSeries k ⊗[PowerSeries k] B))
