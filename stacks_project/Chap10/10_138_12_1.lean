/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Smooth.Quotient
import StacksCheckRecall

@[expose] public section

/-!
# The conormal sequence in square-zero descent

The displayed sequence `10.138.12.1` is the source-facing specialization used in the proof of
Lemma 10.138.12.  Its reusable ingredients are the canonical conormal exact sequence and the
split-injection criterion for formal smoothness; this file only records the polynomial-presentation
bridge between those APIs.

@stack 031M
-/

open scoped TensorProduct
open Algebra.Extension

universe u v w

noncomputable section

variable {R : Type u} {S : Type v} {ι : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R)
variable [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]

/-- Equation 10.138.12.1: under the hypotheses of Lemma 10.138.12, the conormal sequence of a
surjective polynomial presentation remains left injective and exact after reduction modulo `I`.

The source term `J / (I J + J^2)` is represented canonically as the base change of the presentation
cotangent module to `S / IS`. -/
@[stacks 031M]
theorem polynomial_presentation_conormal_sequence_mod_ideal
    [Module.Flat R S]
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S))
    (_hI_square_zero : I * I = ⊥)
    (_hSmooth : Algebra.FormallySmooth (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I)) :
    let P : Algebra.Extension R S :=
      Algebra.Extension.ofSurjective
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    let Sbar := S ⧸ Ideal.map (algebraMap R S) I
    Function.Injective (LinearMap.baseChange Sbar P.cotangentComplex) ∧
      Function.Exact
        (LinearMap.baseChange Sbar P.cotangentComplex)
        (LinearMap.baseChange Sbar P.toKaehler) := sorry

@[stacks 031M "split-injection criterion"]
#check @Algebra.Extension.formallySmooth_iff_split_injection

@[stacks 031M "right-exact conormal sequence"]
#check @KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange

@[stacks 031M "surjective differential map"]
#check @KaehlerDifferential.mapBaseChange_surjective
