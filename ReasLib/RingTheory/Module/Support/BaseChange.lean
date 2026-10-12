/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Support under scalar extension

This leaf owns the support formula for the canonical tensor-product base
change.  The ambient algebra map is the only structural input; chapter files
should use this owner instead of carrying a numbered theorem name.

@stack 0BUR
-/

@[expose] public section

universe u v w

open PrimeSpectrum
open scoped TensorProduct

namespace Module

variable {R : Type u} {R' : Type v} {M : Type w}
variable [CommRing R] [CommRing R'] [Algebra R R']
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The support of a finite module after scalar extension is the inverse image
of the original support along the induced map on prime spectra. -/
@[stacks 0BUR "support under tensor-product scalar extension"]
theorem support_tensorProduct_eq_preimage_comap :
    support R' (R' ⊗[R] M) =
      PrimeSpectrum.comap (algebraMap R R') ⁻¹' support R M := sorry

/-- Full support is preserved by tensor-product scalar extension. -/
theorem support_tensorProduct_eq_univ_of_support_eq_univ
    (hsupp : support R M = Set.univ) :
    support R' (R' ⊗[R] M) = Set.univ := sorry

end Module
