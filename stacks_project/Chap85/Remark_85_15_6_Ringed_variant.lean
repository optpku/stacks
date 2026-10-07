module

public import stacks_project.Chap85.Remark_85_15_6_Ringed_variant_Ringed
import StacksCheckRecall

/- Remark 85.15.6 (Ringed variant) (1): a ringed site (C / K, O_K) for K in SR(C),
with O_K = j⁻¹ O_C. -/
@[stacks 0D9U] #check @RingedSite.Localization.AtSR.site

/- Remark 85.15.6 (Ringed variant) (2): the decomposition
Mod(O_K) ≌ ∏ᵢ Mod(O_{U_i}) if K = {U_i}. -/
@[stacks 0D9U] #check @RingedSite.Localization.AtSR.modulesEquiv

/- Remark 85.15.6 (Ringed variant) (3): the localization morphism of ringed topoi
j : (Sh(C / K), O_K) ⟶ (Sh(C), O_C). -/
@[stacks 0D9U] #check @RingedSite.Localization.AtSR.toAmbient

/- Remark 85.15.6 (Ringed variant) (4): a morphism of ringed topoi
f : (Sh(C / K), O_K) ⟶ (Sh(C / L), O_L) for f : K ⟶ L in SR(C). -/
@[stacks 0D9U] #check @RingedSite.Localization.AtSR.map

/- Remark 85.15.6 (Ringed variant) (5): j^* has an exact left adjoint
j_! : Mod(O_K) ⥤ Mod(O_C), which sends (F_i)_i to ⊕ᵢ j_{i,!} F_i. -/
@[stacks 0D9U] #check @RingedSite.Localization.AtSR.moduleLowerShriek_exact
@[stacks 0D9U] #check @RingedSite.Localization.AtSR.moduleLowerShriekCoprod_isIso

/- Remark 85.15.6 (Ringed variant) (6): f^* has an exact left adjoint
f_! : Mod(O_K) ⥤ Mod(O_L). -/
@[stacks 0D9U] #check @RingedSite.Localization.AtSR.map_moduleLowerShriek_exact
@[stacks 0D9U] #check @RingedSite.Localization.AtSR.mapModuleLowerShriek_adjunction

/- Remark 85.15.6 (Ringed variant) (7): j^* and f^* are exact, i.e. j and f are
flat morphisms of ringed topoi. -/
@[stacks 0D9U] #check @RingedSite.Localization.AtSR.toAmbient_modulePullback_exact
@[stacks 0D9U] #check @RingedSite.Localization.AtSR.map_modulePullback_exact
