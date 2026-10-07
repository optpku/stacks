module

public import ReasLib.RingTheory.Flatness.NilpotentFiber
import StacksCheckRecall

/-!
# The nilpotent case of the fiberwise flatness criterion

@stack 06A5
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

section

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable {I : Ideal R} [AddCommGroup M] [Module S' M]

/- Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case) (1): for a nilpotent
ideal `I ⊂ R`, flatness of the canonical quotient module over `S / IS`, together with
R-flatness of the restricted `S'`-module, gives S-flatness. -/
@[stacks 06A5 "(1)"]
#check (Module.Flat.Nilpotent.of_quotient_flat_of_flat_tower :
  ∀ {I : Ideal R}, IsNilpotent I →
    Module.Flat (S ⧸ Ideal.map (algebraMap R S) I)
      ((RestrictScalars S S' M) ⧸
        (Ideal.map (algebraMap R S) I •
          (⊤ : Submodule S (RestrictScalars S S' M)))) →
    Module.Flat R (RestrictScalars R S' M) →
    Module.Flat S (RestrictScalars S S' M))

/- Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case) (2): under the same
nilpotent quotient and base-flatness hypotheses, every prime `q : PrimeSpectrum S` with
nontrivial fiber `M ⊗[S] q.asIdeal.ResidueField` has `(algebraMap R (Localization.AtPrime q.asIdeal)).Flat`. -/
@[stacks 06A5 "(2)"]
#check (RingHom.Flat.Nilpotent.atPrime_of_quotient_flat :
  ∀ {I : Ideal R}, IsNilpotent I →
    Module.Flat (S ⧸ Ideal.map (algebraMap R S) I)
      ((RestrictScalars S S' M) ⧸
        (Ideal.map (algebraMap R S) I •
          (⊤ : Submodule S (RestrictScalars S S' M)))) →
    Module.Flat R (RestrictScalars R S' M) →
    ∀ q : PrimeSpectrum S,
      Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField) →
        (algebraMap R (Localization.AtPrime q.asIdeal)).Flat)

end
