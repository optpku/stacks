module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.PullbackSections

/-!
# Flatness of restriction from the small étale site to the small Zariski site
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

/-- The canonical morphism from the small étale ringed site of a scheme to its small
Zariski ringed site is flat. -/
theorem smallEtaleToZariski_isFlat (S : Scheme.{u}) :
    RingedSite.Hom.IsFlat.{u} (smallEtaleToZariski S) := sorry

end AlgebraicGeometry.Scheme.SiteRestriction
