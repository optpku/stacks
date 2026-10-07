module

public import Mathlib.CategoryTheory.Sites.Over
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap66.Lemma_66_18_6

/-!
# Affine étale ringed site of an algebraic space

The structure sheaf `𝒪_X` on the affine étale site of an algebraic space `X` is the restriction
of the small étale structure sheaf along `affineEtaleInclusion`. This packages the ringed site
`(X_affine,étale, 𝒪_X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure sheaf `𝒪_X` on the affine étale site of an algebraic space, obtained by
restricting the small étale structure sheaf along `affineEtaleInclusion`. -/
def affineStructureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (affineEtaleTopology X) RingCat.{u} :=
  ((affineEtaleInclusion X).sheafPushforwardContinuous RingCat.{u}
      (affineEtaleTopology X) (smallEtaleTopology X)).obj (structureSheaf X)

/-- On an affine scheme étale over `X`, the affine structure sheaf agrees with `𝒪_X`. -/
theorem affineStructureSheaf_obj_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : affineEtaleSite X) :
    (affineStructureSheaf X).obj.obj (op U) = (structureSheaf X).obj.obj (op U.obj) :=
  rfl

/-- On an affine scheme étale over `X`, the affine structure sheaf has value `Γ(U, 𝒪_U)`. -/
theorem affineStructureSheaf_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : affineEtaleSite X) :
    (affineStructureSheaf X).obj.obj (op U) = RingCat.of Γ(U.obj.left.left, ⊤) :=
  sorry

/-- The affine étale site of `X`, equipped with its structure sheaf. -/
abbrev affineRingedSite {S : Scheme.{u}} (X : AlgebraicSpace S) : RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf (affineEtaleTopology X) (affineStructureSheaf X)

/-- The structure sheaf of `affineRingedSite X` is the restricted structure sheaf. -/
theorem affineRingedSite_structureSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineRingedSite X).structureSheaf = affineStructureSheaf X :=
  rfl

/-- The site topology of `affineRingedSite X` is `affineEtaleTopology X`. -/
theorem affineRingedSite_siteTopology {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineRingedSite X).siteTopology = affineEtaleTopology X :=
  rfl

/-- Abelian-group-valued sheaf composition exists on the affine étale topology of an algebraic
space. -/
instance affineEtaleTopology_hasSheafCompose {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (affineEtaleTopology X).HasSheafCompose
      (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Abelian-group-valued weak sheafification exists on the affine étale topology of an algebraic
space. -/
instance affineEtaleTopology_hasWeakSheafify {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasWeakSheafify (affineEtaleTopology X) AddCommGrpCat.{u} :=
  sorry

/-- On the affine étale topology of an algebraic space, sheafification equivalences are the
locally bijective morphisms. -/
instance affineEtaleTopology_wEqualsLocallyBijective {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    (affineEtaleTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

/-- Abelian-group-valued sheaf composition exists on every slice of the affine étale topology of
an algebraic space. -/
instance affineEtaleTopology_over_hasSheafCompose {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ∀ U : affineEtaleSite X,
      ((affineEtaleTopology X).over U).HasSheafCompose
        (forget₂ RingCat.{u} AddCommGrpCat.{u}) :=
  sorry

/-- Abelian-group-valued weak sheafification exists on every slice of the affine étale topology of
an algebraic space. -/
instance affineEtaleTopology_over_hasWeakSheafify {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ∀ U : affineEtaleSite X,
      HasWeakSheafify ((affineEtaleTopology X).over U) AddCommGrpCat.{u} :=
  sorry

/-- On every slice of the affine étale topology of an algebraic space, sheafification equivalences
are the locally bijective morphisms. -/
instance affineEtaleTopology_over_wEqualsLocallyBijective {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    ∀ U : affineEtaleSite X,
      ((affineEtaleTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
