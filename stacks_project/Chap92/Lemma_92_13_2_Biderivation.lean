module

public import ReasLib.RingTheory.MvPolynomial.Biderivation

@[expose] public section
universe u

/- The polynomial biderivation constructor for compatible generator values. -/
#check (MvPolynomial.mkBiderivation :
  ∀ (R : Type u) [CommRing R] {σ : Type u} {M : Type u}
    [AddCommGroup M] [Module R M]
    [Module (MvPolynomial σ R) M] [Module (MvPolynomial σ R)ᵐᵒᵖ M]
    [IsScalarTower R (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R)ᵐᵒᵖ M]
    [SMulCommClass (MvPolynomial σ R) (MvPolynomial σ R)ᵐᵒᵖ M]
    (m : σ → M) (hm : MvPolynomial.BiderivationCompatible R m),
    Biderivation R (MvPolynomial σ R) M)
