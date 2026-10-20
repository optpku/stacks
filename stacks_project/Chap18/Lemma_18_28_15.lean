module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat.SquareZero
import StacksCheckRecall

/-!
# Lemma 18.28.15

Flatness across a square-zero reduction is controlled by flatness of the quotient module and
monicity of the kernel-action map.  The reusable owner packages both defining short exact
sequences and formulates the square-zero condition intrinsically in the monoidal category.
-/

@[expose] public section

/- Lemma 18.28.15 (08M4): the square-zero flatness criterion. -/
@[stacks 08M4]
#check @SheafOfModules.RingedSite.IsSquareZeroReduction.isFlat_iff

/- Reusable reduction data and its standard projections. -/
#check @SheafOfModules.RingedSite.IsSquareZeroReduction
#check @SheafOfModules.RingedSite.IsSquareZeroReduction.ideal_spec
#check @SheafOfModules.RingedSite.IsSquareZeroReduction.quotient_spec
#check @SheafOfModules.RingedSite.IsSquareZeroReduction.idealInclusion_mono
#check @SheafOfModules.RingedSite.IsSquareZeroReduction.structureMap_epi
#check @SheafOfModules.RingedSite.IsSquareZeroReduction.quotient_epi
