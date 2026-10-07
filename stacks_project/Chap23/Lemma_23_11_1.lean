module

public import ReasLib.RingTheory.Ideal.Cotangent.ProjectiveDimension
import StacksCheckRecall

@[expose] public section

/- Lemma 23.11.1 (tag `0FJQ`): a complemented rank-one summand of `I / I²` lifts to a
nonzerodivisor in `I` which generates that summand. -/
universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {I : Ideal R}
variable {F : Submodule (R ⧸ I) I.Cotangent}
variable (hpd : CategoryTheory.projectiveDimension (ModuleCat.of R I) ≠ ⊤)
variable (hFcompl : IsComplemented F)
variable (hF : Nonempty (F ≃ₗ[R ⧸ I] (R ⧸ I)))

@[stacks 0FJQ]
#check (Ideal.Cotangent.exists_nonzerodivisor_lifting hpd hFcompl hF :
  ∃ x : I,
    (x : R) ∈ nonZeroDivisors R ∧
      Submodule.span (R ⧸ I) {I.toCotangent x} = F)

end
