/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.PolynomialPoincare
public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers.PolynomialPoincare.Adic
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DPPolynomial.DeRham
open scoped TensorProduct

universe u

/- Lemma 60.20.2 (1): adjoining divided-power polynomial variables preserves the
de Rham quasi-isomorphism for an integrable connection. -/
@[stacks 07LD] #check (DPPolynomial.DeRham.dpPolynomial_deRhamComparison_quasiIso :
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) (ι : Type u)
    {M : Type u} [AddCommGroup M] [Module B M]
    (conn : Connection (derivationB A B δ) M)
    (hconn : Connection.IsIntegrable conn (canonicalCalculus A B δ)),
    QuasiIso (scalarExtensionComparison A B δ ι conn hconn))

/- Lemma 60.20.2 (2): after p-adic completion, adjoining divided-power
polynomial variables preserves the de Rham quasi-isomorphism for a complete
module with an integrable completed-valued connection. -/
@[stacks 07LD] #check (DPPolynomial.DeRham.dpPolynomial_completedDeRhamComparison_quasiIso :
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {J : Ideal B} (δ : DividedPowers J) (ι : Type u) (p : ℕ)
    {M : Type u} [AddCommGroup M] [Module (completedRingB B p) M]
    [IsAdicComplete (principalIdealB (completedRingB B p) p) M]
    (conn : Connection.Adic A B δ p M)
    (hconn : Connection.Adic.IsIntegrable A B δ p conn),
    QuasiIso (adicComparison A B δ ι p conn hconn))

end
