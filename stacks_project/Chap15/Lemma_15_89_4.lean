/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.IdealPower.Serre
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.89.4

@stack 05EB
-/

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Lemma 15.89.4 (1) (Stacks 05EB): quotienting by the primary component leaves no
stage-one `I`-power torsion. -/
@[stacks 05EB]
#check fun (I : Ideal R) (hI : I.FG) ↦
  (Ideal.powerTorsion_quotient_primaryComponent_eq_bot (M := M) I hI :
    I.powerTorsion (M ⧸ I.primaryComponent M) 1 = ⊥)

/- Lemma 15.89.4 (2) (Stacks 05EB): ideal-power torsion is closed under extensions. -/
@[stacks 05EB]
#check fun (I : Ideal R) (N : Submodule R M)
    (hN : Module.IsIdealPowerTorsion I N)
    (hQ : Module.IsIdealPowerTorsion I (M ⧸ N)) ↦
  (Module.isIdealPowerTorsion_of_submodule_quotient I N hN hQ :
    Module.IsIdealPowerTorsion I M)

end
