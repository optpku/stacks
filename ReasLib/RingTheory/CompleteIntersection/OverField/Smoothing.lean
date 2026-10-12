/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.CompleteIntersection.OverField

@[expose] public section

universe u v

open scoped TensorProduct

namespace IsGlobalCompleteIntersection

/-- Every global complete intersection over a field admits a flat finite-type power-series
algebra model with the given special fibre and a smooth Laurent-series generic fibre. -/
theorem exists_flat_finiteType_smoothing {k : Type u} [Field k] {A : Type v}
    [CommRing A] [Algebra k A] [IsGlobalCompleteIntersection k A] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra (PowerSeries k) B)
      (_ : Algebra k B) (_ : IsScalarTower k (PowerSeries k) B)
      (_ : Module.Flat (PowerSeries k) B) (_ : Algebra.FiniteType (PowerSeries k) B)
      (e : (B ⧸ Ideal.span {(algebraMap (PowerSeries k) B) (PowerSeries.X : PowerSeries k)}) ≃ₐ[k] A),
      Algebra.Smooth (LaurentSeries k) (LaurentSeries k ⊗[PowerSeries k] B) := sorry

end IsGlobalCompleteIntersection

namespace IsLocalCompleteIntersection

/-- Every finite-dimensional local complete-intersection algebra over a field admits a
finite flat power-series algebra model with the given special fibre and an étale
Laurent-series generic fibre. -/
theorem exists_flat_finite_etale_smoothing {k : Type u} [Field k] {A : Type v}
    [CommRing A] [Algebra k A] [FiniteDimensional k A] [IsLocalCompleteIntersection k A] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra (PowerSeries k) B)
      (_ : Algebra k B) (_ : IsScalarTower k (PowerSeries k) B)
      (_ : Module.Flat (PowerSeries k) B) (_ : Module.Finite (PowerSeries k) B)
      (e : (B ⧸ Ideal.span {(algebraMap (PowerSeries k) B) (PowerSeries.X : PowerSeries k)}) ≃ₐ[k] A),
      Algebra.Etale (LaurentSeries k) (LaurentSeries k ⊗[PowerSeries k] B) := sorry

end IsLocalCompleteIntersection
