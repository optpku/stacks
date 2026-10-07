module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat.BaseChange
import StacksCheckRecall

/-!
# Lemma 18.28.16

Flat same-site base change is invisible on module sheaves uniformly annihilated by a power of an
ideal when the induced map on quotient ring sheaves is an isomorphism.  Quotient carriers and
maps are owned by the neutral ideal-quotient leaf.
-/

@[expose] public section

/- Lemma 18.28.16 (0GLY): the ideal-power torsion flat base-change criterion. -/
@[stacks 0GLY]
#check @SheafOfModules.RingedSite.IdealPower.IsAnnihilated.baseChangeUnit_isIso

/- Reusable hypotheses and quotient comparison. -/
#check @SheafOfModules.RingedSite.IsFlatHom
#check @SheafOfModules.RingedSite.IdealPower.IsAnnihilated
#check @SheafOfModules.RingedSite.IdealSheaf.TargetQuotient.ringMap
