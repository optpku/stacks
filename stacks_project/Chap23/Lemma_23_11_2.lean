module

public import ReasLib.RingTheory.Ideal.Cotangent.ProjectiveDimension
import StacksCheckRecall

@[expose] public section

/- Lemma 23.11.2 (tag `0FJR`): a complemented free rank-`r` summand of `I / I²` lifts to a
regular sequence in `I` whose cotangent classes generate the summand. -/
universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {I : Ideal R} {r : ℕ}
variable {F : Submodule (R ⧸ I) I.Cotangent}
variable (hpd : CategoryTheory.projectiveDimension (ModuleCat.of R I) ≠ ⊤)
variable (hFcompl : IsComplemented F)
variable (hF : Nonempty (F ≃ₗ[R ⧸ I] (Fin r → R ⧸ I)))

@[stacks 0FJR]
#check (Ideal.Cotangent.exists_regularSequence_lifting hpd hFcompl hF :
  ∃ x : Fin r → I,
    RingTheory.Sequence.IsRegular R (List.ofFn fun i ↦ (x i : R)) ∧
      Submodule.span (R ⧸ I) (Set.range fun i ↦ I.toCotangent (x i)) = F)

end

#check @Ideal.Cotangent.exists_regularSequence_lifting_of_rank
