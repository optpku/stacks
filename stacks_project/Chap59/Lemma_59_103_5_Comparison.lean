module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.DerivedComparison
public import stacks_project.Chap59.Lemma_59_103_4_Situation
public import stacks_project.Chap59.Lemma_59_103_4_TorsionPullback

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.HComparison

/-- Abelian sheaves on the small étale site have injective resolutions. -/
instance smallEtale_hasInjectiveResolutions_addCommGrp (X : Scheme.{u}) :
    HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  PhComparison.smallEtale_hasInjectiveResolutions X

/-- The inclusion of abelian sheaves into presheaves on the small étale site
admits a left adjoint. -/
instance smallEtale_hasWeakSheafify_addCommGrp (X : Scheme.{u}) :
    HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (PhComparison.smallEtale_hasSheafify_addCommGrp X).isRightAdjoint

/-- The inclusion of abelian sheaves into presheaves on the big h slice
admits a left adjoint. -/
instance hOver_hasWeakSheafify_addCommGrp (X : Scheme.{u}) :
    HasWeakSheafify (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1} :=
  (hOver_hasSheafify_addCommGrp X).isRightAdjoint

end AlgebraicGeometry.Scheme.HComparison

/- The small-to-h inverse image on abelian sheaves. -/
#check (AlgebraicGeometry.Scheme.HComparison.aInverseImage :
  ∀ (X : Scheme.{u}),
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf (hPrecoverage.toGrothendieck.over X) AddCommGrpCat.{u + 1})

end
