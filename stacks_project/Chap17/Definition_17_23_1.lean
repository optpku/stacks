module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Annihilator
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Annihilator
import StacksCheckRecall

@[expose] public section

/- Definition 17.23.1 (0H2H): the annihilator of `F` is the kernel subobject of the canonical
action map from the structure module to the internal endomorphism sheaf of `F`. -/
@[stacks 0H2H]
#check @SheafOfModules.Annihilator.subobject

/- The underlying module sheaf, canonical action map, inclusion, and kernel equation are reusable
named views of the subobject owner. -/
#check @SheafOfModules.annihilator
#check @SheafOfModules.Annihilator.action
#check @SheafOfModules.Annihilator.ι
#check @SheafOfModules.Annihilator.ι_comp_action
#check @SheafOfModules.Annihilator.factors_iff
#check @SheafOfModules.Annihilator.lift
#check @SheafOfModules.Annihilator.hom_ext
#check @SheafOfModules.Annihilator.mapIso
#check @SheafOfModules.Annihilator.mapIso_hom_ι

/- The point-free kernel owner is defined for arbitrary commutative ringed sites; the
ringed-space declarations above are only the source-facing specialization. -/
#check @SheafOfModules.RingedSite.Annihilator.action
#check @SheafOfModules.RingedSite.Annihilator.subobject
#check @SheafOfModules.RingedSite.Annihilator.factors_iff
#check @SheafOfModules.RingedSite.Annihilator.lift
#check @SheafOfModules.RingedSite.Annihilator.hom_ext
#check @SheafOfModules.RingedSite.Annihilator.subobject_eq_of_iso
#check @SheafOfModules.RingedSite.Annihilator.mapIso
#check @SheafOfModules.RingedSite.Annihilator.mapIso_hom_ι

/- The image of an annihilator section is a structure-sheaf section acting trivially on `F`. -/
#check @SheafOfModules.Annihilator.sectionToRing
#check @SheafOfModules.Annihilator.sectionToRing_smul_eq_zero
