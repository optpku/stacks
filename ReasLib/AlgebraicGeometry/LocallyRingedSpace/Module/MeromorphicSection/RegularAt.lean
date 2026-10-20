module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.MeromorphicSection

/-!
# Pointwise regularity of meromorphic sections

A meromorphic section of a module sheaf is regular at a point when its germ lies in the image of
the canonical map from the original module stalk to the meromorphic-section stalk.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.MeromorphicSection

open TopologicalSpace

variable {X : LocallyRingedSpace.{u}}
variable {L : SheafOfModules.RingedSite.ringedSiteModuleCategory
  (Opens.grothendieckTopology X.toTopCat) X.𝒪}

/-- A meromorphic section is regular at a point when its germ comes from the original module
stalk. -/
def IsRegularAt (s : X.meromorphicSections L) (x : X) : Prop :=
  ∃ t : (SheafOfModules.stalkFunctorOfCommRing X.𝒪 x).obj L,
    X.meromorphicSectionStalkMap L x t =
      SheafOfModules.sectionGermOfCommRing s x

/-- Pointwise regularity of a meromorphic section is equivalent to the existence of a module-stalk
element mapping to its germ. -/
theorem isRegularAt_iff (s : X.meromorphicSections L) (x : X) :
    IsRegularAt s x ↔
      ∃ t : (SheafOfModules.stalkFunctorOfCommRing X.𝒪 x).obj L,
        X.meromorphicSectionStalkMap L x t =
          SheafOfModules.sectionGermOfCommRing s x := sorry

end AlgebraicGeometry.LocallyRingedSpace.MeromorphicSection
