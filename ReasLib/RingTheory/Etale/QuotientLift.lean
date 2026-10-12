/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Core
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Etale lifting across a quotient

This leaf owns the existence statement for lifting an etale algebra over `R ⧸ I` to an etale
`R`-algebra.  The quotient comparison is kept as an explicit `AlgEquiv` witness, so the owner
does not choose a presentation or a particular lift.

@stack 04D1
-/

@[expose] public section

universe u v

namespace Algebra.Etale

variable {R : Type u} [CommRing R] (I : Ideal R) {Sbar : Type v}
variable [CommRing Sbar] [Algebra (R ⧸ I) Sbar] [Algebra.Etale (R ⧸ I) Sbar]

/-- A quotient etale algebra admits an etale lift to the base ring, with its reduction identified
by an algebra equivalence over `R ⧸ I`.  The witness is existential source data rather than a
chosen construction, so no noncanonical lift is exposed as a public definition. -/
@[stacks 04D1 "etale lift over a quotient"]
theorem exists_lift_of_quotient :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S) (_ : Algebra.Etale R S),
      Nonempty ((S ⧸ Ideal.map (algebraMap R S) I) ≃ₐ[R ⧸ I] Sbar) := sorry

end Algebra.Etale
