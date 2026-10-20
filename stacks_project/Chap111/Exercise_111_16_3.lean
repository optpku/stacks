module

import ReasLib.LinearAlgebra.FiniteDimensional.Field
import ReasLib.RingTheory.Jacobson.FiniteType
import ReasLib.RingTheory.PowerSeries.NonFiniteType
import Mathlib.Data.Complex.Basic
import StacksCheckRecall

@[expose] public section

universe u v

/- Exercise 111.16.3 (1): if `R` is a domain and a finite-dimensional algebra over a field `k`,
then `R` is a field. -/
@[stacks 02DP] #check (FiniteDimensional.isField_of_domain :
  ∀ (k : Type u) [Field k] (R : Type v) [CommRing R] [IsDomain R] [Algebra k R]
    [FiniteDimensional k R], IsField R)

/- Exercise 111.16.3 (2): in a finitely generated algebra over a field, a non-nilpotent element
misses some maximal ideal. -/
@[stacks 02DP] #check (Algebra.FiniteType.exists_isMaximal_notMem_of_not_isNilpotent :
  ∀ (k : Type u) [Field k] (R : Type v) [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] {f : R}, ¬ IsNilpotent f → ∃ m : Ideal R, m.IsMaximal ∧ f ∉ m)

/- The formal power series ring `PowerSeries k` is not of finite type as a `k`-algebra. -/
#check (PowerSeries.not_finiteType : ∀ (k : Type u) [Field k],
  ¬ Algebra.FiniteType k (PowerSeries k))

/- The indeterminate `X` is not nilpotent in `PowerSeries k`. -/
#check (PowerSeries.not_isNilpotent_X : ∀ (k : Type u) [Field k],
  ¬ IsNilpotent (PowerSeries.X : PowerSeries k))

/- Exercise 111.16.3 (3): the conclusion of Exercise 111.16.3 (2) fails for `PowerSeries k`,
which is not of finite type over the field `k`: every maximal ideal contains `X`. -/
@[stacks 02DP] #check (PowerSeries.not_exists_isMaximal_notMem_X :
  ∀ (k : Type u) [Field k],
    ¬ ∃ m : Ideal (PowerSeries k), m.IsMaximal ∧ PowerSeries.X ∉ m)

/- Exercise 111.16.3 (4): every radical ideal of `MvPolynomial (Fin n) ℂ` equals the intersection
of the maximal ideals containing it, recorded as `I.jacobson`. -/
@[stacks 02DP] #check (MvPolynomial.eq_jacobson_of_isRadical :
  ∀ {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}, I.IsRadical → I = I.jacobson)
