/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.DividedPowers.Polynomial.Shift
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.PolynomialPoincare

@[expose] public section

open CategoryTheory DPPolynomial DPPolynomial.Finite DPPolynomial.DeRham
open scoped TensorProduct

universe u

section

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
variable {J : Ideal B} (δ : DividedPowers J)
variable {M : Type} [AddCommGroup M] [Module B M]
variable (conn : Connection (derivationB A B δ) M)
variable (hconn : Connection.IsIntegrable conn (canonicalCalculus A B δ))

/- Example 60.25.2 -/
@[stacks 07Q8]
#check (DPPolynomial.DeRham.dpPolynomial_deRhamComparison_quasiIso A B δ (Fin 1) conn hconn :
  QuasiIso (DPPolynomial.DeRham.scalarExtensionComparison A B δ (Fin 1) conn hconn))

end

/- The extended ideal in a divided-power polynomial algebra. -/
#check (DPPolynomial.ideal_def :
  ∀ (A : Type u) [CommSemiring A] (ι : Type u) (I : Ideal A),
    DPPolynomial.ideal A ι I =
      I.map (algebraMap A (DPPolynomial A ι)) + DPPolynomial.positiveIdeal A ι)

/- Canonical divided powers of polynomial variables. -/
#check (DPPolynomial.dividedPowers_dpow_X (ι := Fin 1) :
  ∀ {A : Type u} [CommSemiring A] {I : Ideal A} (γ : DividedPowers I)
    (n : ℕ) (i : Fin 1),
    (DPPolynomial.dividedPowers γ).dpow n (DPPolynomial.X A i) =
      DPPolynomial.dp A n i)

/- Scalar-weighted shift of a divided-power monomial. -/
#check (DPPolynomial.Finite.shift_smul_dp :
  ∀ {B : Type u} [CommRing B] (b : B) (m : ℕ),
    DPPolynomial.Finite.shift
        (algebraMap B (DPPolynomial.Finite.Ring B 1) b *
          DPPolynomial.dp B m (0 : Fin 1)) =
      algebraMap B (DPPolynomial.Finite.Ring B 1) b *
        DPPolynomial.dp B (m + 1) (0 : Fin 1))

/- Constant-term identity for the divided-power shift. -/
#check (DPPolynomial.Finite.sub_shift_partialZ :
  ∀ {B : Type u} [CommRing B] (f : DPPolynomial.Finite.Ring B 1),
    f - DPPolynomial.Finite.shift (DPPolynomial.Finite.partialZ f) =
      algebraMap B (DPPolynomial.Finite.Ring B 1)
        (DPPolynomial.Finite.constantTerm f))
