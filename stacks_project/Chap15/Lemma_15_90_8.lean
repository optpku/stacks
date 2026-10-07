module

public import ReasLib.Algebra.Category.ModuleCat.Ext.IdealPower.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.90.8: Ext base change for ideal-power torsion modules

@stack 05EG
-/

noncomputable section

open CategoryTheory

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R) (hI : I.FG)
variable (M N : ModuleCat.{u} R)
variable (hflat : (algebraMap R S).Flat)
variable (hM : Module.IsIdealPowerTorsion I M)
variable (hquot : Function.Bijective ((algebraMap R S).quotientByIdeal I))

/- Lemma 15.90.8: under formal-glueing hypotheses, every degree-one extension after base
change descends from an extension over the source ring. -/
@[stacks 05EG]
#check (ModuleCat.Ext.IdealPower.BaseChange.map_surjective
    (algebraMap R S) I hI M N hflat hM hquot :
  Function.Surjective
    (ModuleCat.Ext.FlatBaseChange.map (algebraMap R S) M N hflat 1))

end
