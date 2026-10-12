/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Inseparable
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.Algebra.Polynomial.Bivariate

@[expose] public section

noncomputable section

open PrimeSpectrum Polynomial
open scoped Polynomial.Bivariate

universe u

namespace GoingUpDown.Polynomial

/-- The map on spectra induced by a field embedding into its polynomial ring is specializing. -/
theorem specializingMap_comap_polynomialOverField {k : Type u} [Field k] :
    SpecializingMap (comap (algebraMap k k[X])) :=
  sorry

/-- The polynomial extension of a field has the going-down property. -/
instance hasGoingDown_polynomialOverField {k : Type u} [Field k] :
    Algebra.HasGoingDown k k[X] :=
  sorry

/-- Adjoining a second polynomial variable to a polynomial ring does not give a specializing map. -/
theorem not_specializingMap_comap_bivariateOverPolynomial {k : Type u} [Field k] :
    ¬ SpecializingMap (comap (algebraMap k[X] k[X][Y])) :=
  sorry

/-- The extension from one polynomial variable to two has the going-down property. -/
instance hasGoingDown_bivariateOverPolynomial {k : Type u} [Field k] :
    Algebra.HasGoingDown k[X] k[X][Y] :=
  sorry

end GoingUpDown.Polynomial
