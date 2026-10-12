/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Remark_85_16_5_Ringed_variant_Ringed
public import stacks_project.Chap85.Remark_85_16_5_Ringed_variant_Shriek
import StacksCheckRecall

/- Setup: on a ringed site (C, O_C) and an object X, the restricted sheaf
O_X = O_C restricted to C/X is the slice ringed site RingedSite.localization. -/
@[stacks 0D9X] #check @RingedSite.localization

/- Setup: the category SR(C, X) of semi-representable objects over X is
SemiRepresentableFamily.OverFamily, i.e. SR(C, X) = SR(C/X). -/
@[stacks 0D9X] #check @CategoryTheory.SemiRepresentableFamily.OverFamily

/- Remark 85.16.6 (Ringed variant over an object) (1): combining Remarks 85.16.4
and 85.16.5, AtSimplicialSR.site on the slice ringed site yields a ringed site
((C/K)_total, O) for a simplicial object K of SR(C, X). -/
@[stacks 0D9X] #check @RingedSite.Localization.AtSimplicialSR.site

/- Remark 85.16.6 (Ringed variant over an object) (2): the morphism of ringed topoi
a : (Sh((C/K)_total), O) ⟶ (Sh(C/X), O_X) is AtSimplicialSR.toAmbient with
ambient the slice ringed site. -/
@[stacks 0D9X] #check @RingedSite.Localization.AtSimplicialSR.toAmbient

/- Remark 85.16.6 (Ringed variant over an object) (3): the morphisms of ringed topoi
a_n : (Sh(C/K_n), O_n) ⟶ (Sh(C/X), O_X) are AtSimplicialSR.stageToAmbient into
the same slice ambient. -/
@[stacks 0D9X] #check @RingedSite.Localization.AtSimplicialSR.stageToAmbient

/- Remark 85.16.6 (Ringed variant over an object) (4): a functor
a_! : Mod(O) ⥤ Mod(O_X) left adjoint to a^*. -/
@[stacks 0D9X] #check @RingedSite.Localization.AtSimplicialSR.moduleLowerShriek_adjunction

/- Remark 85.16.6 (Ringed variant over an object) (5): exact functors
a_{n!} : Mod(O_n) ⥤ Mod(O_X) left adjoint to a_n^* (in general a_! is not exact). -/
@[stacks 0D9X] #check @RingedSite.Localization.AtSR.moduleLowerShriek_exact

/- Remark 85.16.6 (Ringed variant over an object) (6): the morphisms a and a_n
are flat. -/
@[stacks 0D9X] #check @RingedSite.Localization.AtSimplicialSR.toAmbient_isFlat
@[stacks 0D9X] #check @RingedSite.Localization.AtSimplicialSR.stageToAmbient_isFlat

/- Remark 85.16.6 (Ringed variant over an object) (7): f_φ is flat and there is an
exact functor f_{φ!} : Mod(O_n) ⥤ Mod(O_m) left adjoint to f_φ^*. -/
@[stacks 0D9X] #check @RingedSite.Localization.AtSimplicialSR.stageMap_isFlat
@[stacks 0D9X] #check @RingedSite.Localization.AtSR.map_moduleLowerShriek_exact

/- Remark 85.16.6 (Ringed variant over an object) (8): g_n is flat and
g_{n!} : Mod(O_n) ⥤ Mod(O) left adjoint to g_n^* is exact. -/
@[stacks 0D9X] #check @RingedSite.Localization.AtSimplicialSR.stageIncl_isFlat
@[stacks 0D9X] #check @RingedSite.Localization.AtSimplicialSR.stageInclModuleLowerShriek_adjunction
@[stacks 0D9X] #check @RingedSite.Localization.AtSimplicialSR.stageIncl_moduleLowerShriek_exact
