/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.Biderivation
import StacksCheckRecall

@[expose] public section
universe u
/- Lemma 92.13.2 (operator-approved local erratum): compatible assignments on commuting polynomial
generators extend uniquely to a biderivation into an arbitrary bimodule. The
generator compatibility is necessary; the two module actions need not coincide.
The uploaded source remains unchanged; no upstream correction is claimed. -/
@[stacks 09CF] #check (MvPolynomial.existsUnique_biderivation :
  ∀ {R : Type u} [CommRing R] {σ : Type u} {M : Type u}
    [AddCommGroup M] [Module R M]
    [Module (MvPolynomial σ R) M] [Module (MvPolynomial σ R)ᵐᵒᵖ M]
    [IsScalarTower R (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R)ᵐᵒᵖ M]
    [SMulCommClass (MvPolynomial σ R) (MvPolynomial σ R)ᵐᵒᵖ M]
    (m : σ → M) (hm : MvPolynomial.BiderivationCompatible R m),
    ∃! D : Biderivation R (MvPolynomial σ R) M,
      ∀ s, D.toLinearMap (MvPolynomial.X s) = m s)
