module

public import stacks_project.Chap92.Lemma_92_13_2_Biderivation
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section
universe u
namespace MvPolynomial

/-- Lemma 92.13.2: arbitrary assignments on polynomial generators extend uniquely
to a biderivation into a bimodule. -/
@[stacks 09CF]
theorem existsUnique_biderivation {R : Type u} [CommRing R] {σ : Type u} {M : Type u}
    [AddCommGroup M] [Module R M]
    [Module (MvPolynomial σ R) M] [Module (MvPolynomial σ R)ᵐᵒᵖ M]
    [IsScalarTower R (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R)ᵐᵒᵖ M]
    [SMulCommClass (MvPolynomial σ R) (MvPolynomial σ R)ᵐᵒᵖ M]
    (m : σ → M) :
    ∃! D : Biderivation R (MvPolynomial σ R) M, ∀ s, D.toLinearMap (X s) = m s := sorry


end MvPolynomial
