module

public import Mathlib.RingTheory.Extension.Presentation.Core
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
public import ReasLib.RingTheory.Etale.QuotientLift
import StacksCheckRecall

/-!
Lemma 10.143.10 (04D1): etale algebras over a quotient lift to the base ring.

The two coefficient lemmas and the quotient comparison equivalence are small source-facing
bridges.  The Jacobian construction belongs to the proof route and is deliberately not part of
the chapter API.

@stack 04D1
-/

@[expose] public section

universe u v

namespace Algebra

section

variable {R : Type u} {Sbar : Type v} [CommRing R] (I : Ideal R)
variable [CommRing Sbar] [Algebra (R ⧸ I) Sbar] [Etale (R ⧸ I) Sbar]

omit [Etale (R ⧸ I) Sbar] in
/-- Coefficients of a presentation over `R ⧸ I` can be lifted along the quotient map. -/
lemma presentation_hasCoeffs_of_quotient {ι : Type*} {σ : Type*}
    [Algebra R Sbar] [IsScalarTower R (R ⧸ I) Sbar]
    (P : Algebra.Presentation (R ⧸ I) Sbar ι σ) :
    P.HasCoeffs R := sorry

omit [Etale (R ⧸ I) Sbar] in
/-- Coefficients of a submersive presentation over `R ⧸ I` lift along the quotient map. -/
lemma submersivePresentation_hasCoeffs_of_quotient {ι : Type*} {σ : Type*}
    [Algebra R Sbar] [IsScalarTower R (R ⧸ I) Sbar]
    [Finite σ] [DecidableEq σ]
    (P : Algebra.SubmersivePresentation (R ⧸ I) Sbar ι σ) :
    P.HasCoeffs R := sorry

/-- The lifted presentation model reduces to the given quotient algebra. -/
noncomputable def reduced_presentation_quotient_equiv {ι : Type*} {σ : Type*}
    [Algebra R Sbar] [IsScalarTower R (R ⧸ I) Sbar]
    (P : Algebra.Presentation (R ⧸ I) Sbar ι σ) [P.HasCoeffs R] :
    (P.ModelOfHasCoeffs R ⧸ Ideal.map (algebraMap R (P.ModelOfHasCoeffs R)) I) ≃ₐ[R ⧸ I] Sbar :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (P.ModelOfHasCoeffs R) I).trans
    (P.tensorModelOfHasCoeffsEquiv R)

/-- Lemma 10.143.10: every etale algebra over the quotient ring `R ⧸ I` lifts to an etale
`R`-algebra whose reduction modulo `I` is isomorphic to the given quotient algebra. -/
@[stacks 04D1]
theorem exists_etale_lift_of_quotient :
    ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S) (_ : Etale R S),
      Nonempty ((S ⧸ Ideal.map (algebraMap R S) I) ≃ₐ[R ⧸ I] Sbar) := sorry

#check @Algebra.Etale
#check @Algebra.Presentation.HasCoeffs
#check @Algebra.TensorProduct.quotIdealMapEquivQuotTensor
#check @Algebra.Etale.exists_lift_of_quotient

end

end Algebra
