module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

/-!
# Spaces-étale ringed site of an algebraic space

The structure sheaf `𝒪_X` on `X_spaces,étale` is the cocontinuous extension of the small
étale structure sheaf along `smallEtaleInclusion`. This packages the ringed site
`(X_spaces,étale, 𝒪_X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure sheaf on the spaces-étale site, extended from the actual small chart family. -/
def spacesStructureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) RingCat.{u} :=
  (EtaleRingedTopos.ringExtension X).obj (structureSheaf X)

/-- The structure ring is the specified small-chart extension of the original structure sheaf. -/
theorem spacesStructureSheaf_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    spacesStructureSheaf X =
      (EtaleRingedTopos.ringExtension X).obj (structureSheaf X) :=
  rfl

/-- The étale site of algebraic spaces over `X`, equipped with its structure sheaf. -/
abbrev spacesRingedSite {S : Scheme.{u}} (X : AlgebraicSpace S) :
    RingedSite.{u + 1, u + 1, u} :=
  RingedSite.ofRingSheaf (spacesEtaleTopology X) (spacesStructureSheaf X)

/-- The structure sheaf of `spacesRingedSite X` is `spacesStructureSheaf X`. -/
theorem spacesRingedSite_structureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (spacesRingedSite X).structureSheaf = spacesStructureSheaf X :=
  rfl

/-- The site topology of `spacesRingedSite X` is `spacesEtaleTopology X`. -/
theorem spacesRingedSite_siteTopology {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (spacesRingedSite X).siteTopology = spacesEtaleTopology X :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
