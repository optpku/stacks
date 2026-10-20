module

public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.PullbackSections

/-!
# Flatness of restriction from the small étale site to the small Zariski site
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

/-- The canonical morphism from the small étale ringed site of a scheme to its small
Zariski ringed site is flat. -/
theorem smallEtaleToZariski_isFlat (S : Scheme.{u}) :
    RingedSite.Hom.IsFlat.{u} (smallEtaleToZariski S) := sorry

/-- Module pullback from the small Zariski site to the small étale site is exact. -/
theorem smallEtaleToZariski_modulePullback_exact (X : Scheme.{u}) :
    CategoryTheory.exactFunctor
      (RingedSite.ModuleCat.{u} (Zariski.Small.ringedSite X))
      (RingedSite.ModuleCat.{u} (Etale.Small.ringedSite X))
      (smallEtaleToZariski X).modulePullback.{u} :=
  (smallEtaleToZariski_isFlat X).exact_pullback

/-- A module on the small Zariski site is zero if its pullback to the small étale site
is zero. -/
theorem smallEtaleToZariski_modulePullback_reflects_isZero
    (X : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Zariski.Small.ringedSite X)) :
    IsZero ((smallEtaleToZariski X).modulePullback.{u}.obj F) → IsZero F := sorry

/-- The kernel of module pullback along `smallEtaleToZariski` consists of zero objects. -/
theorem smallEtaleToZariski_modulePullback_kernel_le_isZero (X : Scheme.{u}) :
    (smallEtaleToZariski X).modulePullback.{u}.kernel ≤ IsZero := sorry

/-- A Zariski module vanishes if and only if its pullback along `smallEtaleToZariski` vanishes. -/
theorem smallEtaleToZariski_modulePullback_isZero_iff
    (X : Scheme.{u}) (F : RingedSite.ModuleCat.{u} (Zariski.Small.ringedSite X)) :
    IsZero ((smallEtaleToZariski X).modulePullback.{u}.obj F) ↔ IsZero F := sorry

end AlgebraicGeometry.Scheme.SiteRestriction
