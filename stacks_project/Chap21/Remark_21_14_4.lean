/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Comparison
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.GlobalSections
import StacksCheckRecall

@[expose] public section

/-!
# Remark 21.14.4

The source statement concerns an arbitrary morphism of ringed topoi.  Its presentation-independent
owner lives under `RingedSite.ToposHom`; the module-valued comparison for a morphism of ringed
sites remains available as a stronger companion retaining the global-sections ring action.
-/

/- Remark 21.14.4 (08J6): `RΓ(Y, Rf_* -) ≅ RΓ(X, -)` for an arbitrary morphism of
site-presented ringed topoi, functorially in the derived coefficient object. -/
@[stacks 08J6 "ringed-topos derived global-sections comparison"]
#check @RingedSite.ToposHom.ModuleSections.pushforward_isomorphic

/- The canonical total right-derived direct image used in the source-facing theorem. -/
#check @RingedSite.ToposHom.modulePushforwardDerived

/- For a morphism presented by ringed sites, the comparison additionally retains the module over
the target global-sections ring. -/
@[stacks 0D6H "ringed-site module-valued derived global-sections comparison"]
#check @RingedSite.Hom.ModuleSections.derivedGlobalSectionsPushforwardComparison

@[stacks 0D6H "ringed-site derived global-sections comparison isomorphism"]
#check @RingedSite.Hom.ModuleSections.derivedGlobalSectionsPushforwardComparison_isIso

/- The ringed-site specialization at one derived object is obtained from the component API. -/
@[stacks 0D6H "ringed-site derived global-sections comparison component"]
#check @RingedSite.Hom.ModuleSections.derivedGlobalSectionsPushforwardComparison_app_isIso
