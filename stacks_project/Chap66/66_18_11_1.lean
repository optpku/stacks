/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap66.Lemma_66_18_12_Restriction
public import stacks_project.Chap66.«66_18_11_1_Restrict»

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- 66.18.11.1: if `f : X ⟶ Y` is étale, restriction of a sheaf of sets along
`etaleRestriction f` equals inverse image along the topos morphism associated to that
functor, i.e. `𝒢|_{X_étale} = f_small⁻¹ 𝒢`. -/
@[stacks 03LQ]
noncomputable def etaleRestrictionSheaf_iso_inverseImage
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] :
    etaleRestrictionSheaf f (Type u) ≅
      (etaleRestriction f).sheafPullbackCocontinuous (Type u)
        (smallEtaleTopology X) (smallEtaleTopology Y) :=
  Functor.isoWhiskerLeft (etaleRestrictionSheaf f (Type u))
      (sheafificationNatIso (smallEtaleTopology X) (Type u)) ≪≫
    Functor.isoWhiskerRight
      ((etaleRestriction f).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type u) (smallEtaleTopology X) (smallEtaleTopology Y))
      (presheafToSheaf (smallEtaleTopology X) (Type u))

/-- The component of sheaf restriction ≅ cocontinuous inverse image at a sheaf of sets is the
sheafification isomorphism of the restricted sheaf. -/
theorem etaleRestrictionSheaf_iso_inverseImage_app
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (𝒢 : Sheaf (smallEtaleTopology Y) (Type u)) :
    (etaleRestrictionSheaf_iso_inverseImage f).app 𝒢 =
      sheafificationIso ((etaleRestrictionSheaf f (Type u)).obj 𝒢) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
