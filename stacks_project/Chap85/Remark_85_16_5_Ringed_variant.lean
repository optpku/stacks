/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap85.Remark_85_16_5_Ringed_variant_Ringed
public import stacks_project.Chap85.Remark_85_16_5_Ringed_variant_Shriek
import StacksCheckRecall

/- Remark 85.16.5 (Ringed variant) (1): a ringed site `((C / K)_total, O)` for a
simplicial object `K` of `SR(C)`, with `O = a⁻¹ O_C`. -/
@[stacks 0D9W] #check @RingedSite.Localization.AtSimplicialSR.site

/- Remark 85.16.5 (Ringed variant) (2): the morphism of ringed topoi
`a : (Sh((C / K)_total), O) ⟶ (Sh(C), O_C)`. -/
@[stacks 0D9W] #check @RingedSite.Localization.AtSimplicialSR.toAmbient

/- Remark 85.16.5 (Ringed variant) (3): the morphisms of ringed topoi
`a_n : (Sh(C / K_n), O_n) ⟶ (Sh(C), O_C)`. -/
@[stacks 0D9W] #check @RingedSite.Localization.AtSimplicialSR.stageToAmbient

/- Remark 85.16.5 (Ringed variant) (4): a functor `a_! : Mod(O) ⥤ Mod(O_C)` left
adjoint to `a^*`, existing by Modules on Sites, Lemma 18.41.1 because
`O = a⁻¹ O_C` (in general not exact). -/
@[stacks 0D9W] #check @RingedSite.Localization.AtSimplicialSR.moduleLowerShriek_adjunction

/- Remark 85.16.5 (Ringed variant) (5): exact functors
`a_{n!} : Mod(O_n) ⥤ Mod(O_C)` left adjoint to `a_n^*`. -/
@[stacks 0D9W] #check @RingedSite.Localization.AtSR.moduleLowerShriek_exact

/- Remark 85.16.5 (Ringed variant) (6): the morphisms `a` and `a_n` are flat. -/
@[stacks 0D9W] #check @RingedSite.Localization.AtSimplicialSR.toAmbient_isFlat
@[stacks 0D9W] #check @RingedSite.Localization.AtSimplicialSR.stageToAmbient_isFlat

/- Remark 85.16.5 (Ringed variant) (7): `f_φ` is flat and there is an exact functor
`f_{φ!} : Mod(O_n) ⥤ Mod(O_m)` left adjoint to `f_φ^*`. -/
@[stacks 0D9W] #check @RingedSite.Localization.AtSimplicialSR.stageMap_isFlat
@[stacks 0D9W] #check @RingedSite.Localization.AtSR.map_moduleLowerShriek_exact

/- Remark 85.16.5 (Ringed variant) (8): `g_n` is flat and `g_{n!} : Mod(O_n) ⥤ Mod(O)`
left adjoint to `g_n^*` is exact. -/
@[stacks 0D9W] #check @RingedSite.Localization.AtSimplicialSR.stageIncl_isFlat
@[stacks 0D9W] #check @RingedSite.Localization.AtSimplicialSR.stageInclModuleLowerShriek_adjunction
@[stacks 0D9W] #check @RingedSite.Localization.AtSimplicialSR.stageIncl_moduleLowerShriek_exact
