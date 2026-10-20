module

public import ReasLib.Algebra.Module.IdealPower.Predicate
import StacksCheckRecall

/-!
# Definition 15.89.1

@stack 05E6

An `R`-module is `I`-power torsion when every element is annihilated by a positive power of `I`.
The principal-ideal specialization is the source notion of `f`-power torsion.
-/

universe u v

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

@[stacks 05E6 "Definition 15.89.1 (1), ideal-power torsion modules"]
#check fun (I : Ideal R) ↦ (Module.IsIdealPowerTorsion I M : Prop)

@[stacks 05E6 "Definition 15.89.1 (1), elementwise ideal-power torsion criterion"]
#check fun (I : Ideal R) ↦
  (Module.isIdealPowerTorsion_iff (M := M) I :
    Module.IsIdealPowerTorsion I M ↔
      ∀ x : M, ∃ n : ℕ+, ∀ a : R, a ∈ I ^ (n : ℕ) → a • x = 0)

@[stacks 05E6 "Definition 15.89.1 (2), element-power torsion modules"]
#check fun (f : R) ↦
  (Module.isIdealPowerTorsion_principalIdeal_iff (M := M) f :
    Module.IsIdealPowerTorsion (principalIdeal f) M ↔
      Module.IsTorsion' M (Submonoid.powers f))

end
