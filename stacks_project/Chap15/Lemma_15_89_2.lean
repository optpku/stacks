module

public import ReasLib.Algebra.Homology.ChainComplex.IdealPowerResolution
import StacksCheckRecall

/-!
# Resolutions of ideal-power torsion modules

Lemma 15.89.2 gives an infinite resolution of an ideal-power torsion module by direct sums of
positive ideal-power quotients.

@stack 05E8
-/

@[expose] public section

open CategoryTheory

universe u

section

variable {R : Type u} [CommRing R]

@[stacks 05E8 "Lemma 15.89.2"]
#check fun (I : Ideal R) (M : ModuleCat.{u} R)
    (hM : Module.IsIdealPowerTorsion I M) ↦
  (ChainComplex.IdealPowerResolution.exists_resolution I M hM :
    ∃ (F : ChainComplex (ModuleCat.{u} R) ℕ)
      (π : F ⟶ (ChainComplex.single₀ (ModuleCat R)).obj M),
      QuasiIso π ∧ ChainComplex.IdealPowerResolution.IsTermwiseQuotientSum I F)

@[stacks 05E8 "termwise quotient-sum predicate"]
#check fun (I : Ideal R) (F : ChainComplex (ModuleCat.{u} R) ℕ) ↦
  (ChainComplex.IdealPowerResolution.IsTermwiseQuotientSum I F : Prop)

@[stacks 05E8 "canonical quotient cover used by the resolution"]
#check fun (I : Ideal R) (M : ModuleCat.{u} R) ↦
  (ModuleCat.IdealPower.Cover.π I M : ModuleCat.IdealPower.Cover.source I M ⟶ M)

end
