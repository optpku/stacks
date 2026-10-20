module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology and derived direct image on ringed sites

This file records the presheaf-level Leray comparison for a morphism of ringed sites and its
sheafified consequence.  The cohomology presheaf is the one obtained from the total right derived
underlying-presheaf functor, rather than from an incorrectly assumed exact forgetful functor.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped RingedSiteCohomology

noncomputable section

universe u v

namespace RingedSite.Hom.modulePushforwardDerived

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)
variable [IsGrothendieckAbelian.{max u v} (ModuleCat X)]
variable [IsGrothendieckAbelian.{max u v} (ModuleCat Y)]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived f) (ModuleQis X)]

/-- Restricting the cohomology presheaf of `K` along the underlying functor of `f` gives the
cohomology presheaf of its derived direct image. -/
@[stacks 0D6I "cohomology presheaf comparison"]
theorem cohomologyPresheaf_isomorphic (K : ModuleDerived X) (q : ℤ) :
    IsIsomorphic
      (f.base.op ⋙ 𝓗'[q](X, K))
      (𝓗'[q](Y, (modulePushforwardDerived f).obj K)) := sorry

/-- Lemma 21.20.6 (0D6I): the underlying additive cohomology sheaf of a derived direct image is
the sheafification of the source cohomology presheaf restricted along the underlying functor. -/
@[stacks 0D6I]
theorem cohomologySheafification_isomorphic
    [HasSheafify Y.siteTopology AddCommGrpCat.{max u v}]
    (K : ModuleDerived X) (q : ℤ) :
    IsIsomorphic
      ((presheafToSheaf Y.siteTopology AddCommGrpCat.{max u v}).obj
        (f.base.op ⋙ 𝓗'[q](X, K)))
      (ModuleDerived.underlyingCohomologySheaf Y
        ((modulePushforwardDerived f).obj K) q) := sorry

end RingedSite.Hom.modulePushforwardDerived
