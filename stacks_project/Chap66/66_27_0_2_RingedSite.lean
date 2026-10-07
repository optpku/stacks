module

public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap66.Lemma_66_18_3
public import stacks_project.Chap66.Lemma_66_29_2_Pullback

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

/-- The structure sheaf `𝒪_X` on the étale site of algebraic spaces over `X`, obtained by
cocontinuous direct image of the small étale structure sheaf along `smallEtaleInclusion`. -/
def spacesStructureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) RingCat.{u} :=
  ((smallEtaleInclusion X).sheafPushforwardCocontinuous RingCat.{u}
      (smallEtaleTopology X) (spacesEtaleTopology X)).obj
    (structureSheaf X)

/-- `spacesStructureSheaf X` is cocontinuous pushforward of `structureSheaf X` along
`smallEtaleInclusion X`. -/
theorem spacesStructureSheaf_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    spacesStructureSheaf X =
      ((smallEtaleInclusion X).sheafPushforwardCocontinuous RingCat.{u}
          (smallEtaleTopology X) (spacesEtaleTopology X)).obj
        (structureSheaf X) :=
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
