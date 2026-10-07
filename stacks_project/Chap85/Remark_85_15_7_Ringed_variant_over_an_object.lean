module

public import stacks_project.Chap85.Remark_85_15_6_Ringed_variant_Ringed
import StacksCheckRecall

open RingedSite.Localization

/- Setup: on a ringed site (C, O_C) and an object U, the restricted sheaf O_U
is the slice ringed site RingedSite.localization, with carrier C/U and
structure sheaf O_C restricted to C/U. -/
@[stacks 0D9V] #check @RingedSite.localization

/- Setup: combining Remark 85.15.5, the category SR(C, X) of
semi-representable objects over X is SemiRepresentableFamily.OverFamily,
i.e. SR(C, X) = SR(C/X). -/
@[stacks 0D9V] #check @CategoryTheory.SemiRepresentableFamily.OverFamily

/- Remark 85.15.7 (Ringed variant over an object) (1): AtSR.site applied to the
slice ringed site yields a ringed site (C/K, O_K) for K in SR(C, X). -/
@[stacks 0D9V] #check @AtSR.site

/- Remark 85.15.7 (Ringed variant over an object) (2): the decomposition
Mod(O_K) ≌ ∏ᵢ Mod(O_{U_i}) if K = {U_i}, as AtSR.modulesEquiv on the slice. -/
@[stacks 0D9V] #check @AtSR.modulesEquiv

/- Remark 85.15.7 (Ringed variant over an object) (3): the localization morphism
of ringed topoi j : (Sh(C/K), O_K) ⟶ (Sh(C/X), O_X) is AtSR.toAmbient with
ambient the slice ringed site. -/
@[stacks 0D9V] #check @AtSR.toAmbient

/- Remark 85.15.7 (Ringed variant over an object) (4): a morphism of ringed topoi
f : (Sh(C/K), O_K) ⟶ (Sh(C/L), O_L) for f : K ⟶ L in SR(C, X), as AtSR.map
on the slice. -/
@[stacks 0D9V] #check @AtSR.map

/- Remark 85.15.7 (Ringed variant over an object) (5): the results of
Remark 85.15.6 hold over an object: j_! is exact, and sends (F_i)_i to
⊕ᵢ j_{i,!} F_i. -/
@[stacks 0D9V] #check @AtSR.moduleLowerShriek_exact
@[stacks 0D9V] #check @AtSR.moduleLowerShriekCoprod_isIso

/- Remark 85.15.7 (Ringed variant over an object) (6): f_! is exact, as the
left adjoint of f^*. -/
@[stacks 0D9V] #check @AtSR.map_moduleLowerShriek_exact
@[stacks 0D9V] #check @AtSR.mapModuleLowerShriek_adjunction

/- Remark 85.15.7 (Ringed variant over an object) (7): j^* and f^* are exact,
i.e. j and f are flat morphisms of ringed topoi. -/
@[stacks 0D9V] #check @AtSR.toAmbient_modulePullback_exact
@[stacks 0D9V] #check @AtSR.map_modulePullback_exact
