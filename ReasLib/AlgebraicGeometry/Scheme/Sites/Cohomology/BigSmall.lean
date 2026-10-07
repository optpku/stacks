module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Small
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Cohomology of an abelian sheaf on the big Zariski site over the identity
scheme agrees with cohomology of its canonical restriction to the small Zariski site. -/
theorem cohomology_isomorphic_zariski
    (S : Scheme.{u})
    (F : Sheaf S.bigZariskiTopology AddCommGrpCat.{u}) (p : ℕ)
    [HasSheafify S.smallZariskiTopology AddCommGrpCat.{u}]
    [HasSheafify S.bigZariskiTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallZariskiTopology AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf S.bigZariskiTopology AddCommGrpCat.{u})] :
    IsIsomorphic
      (CategoryTheory.Sheaf.H'
        (((Zariski.SmallToBig.relocalizationFunctor (𝟙 S)).sheafPushforwardContinuous
            AddCommGrpCat.{u} S.smallZariskiTopology S.bigZariskiTopology).obj F)
        p (MorphismProperty.Over.mk _ (𝟙 S) inferInstance))
      (CategoryTheory.Sheaf.H' F p
        ((Zariski.SmallToBig.relocalizationFunctor (𝟙 S)).obj
          (MorphismProperty.Over.mk _ (𝟙 S) inferInstance))) := sorry

/-- Cohomology of an abelian sheaf on the big étale site over the identity
scheme agrees with cohomology of its canonical restriction to the small étale site. -/
theorem cohomology_isomorphic_etale
    (S : Scheme.{u})
    (F : Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}) (p : ℕ)
    [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})] :
    IsIsomorphic
      (CategoryTheory.Sheaf.H'
        (((Etale.SmallToBig.relocalizationFunctor (𝟙 S)).sheafPushforwardContinuous
            AddCommGrpCat.{u} S.smallEtaleTopology (S.overGrothendieckTopology @Etale)).obj F)
        p (MorphismProperty.Over.mk _ (𝟙 S) inferInstance))
      (CategoryTheory.Sheaf.H' F p
        ((Etale.SmallToBig.relocalizationFunctor (𝟙 S)).obj
          (MorphismProperty.Over.mk _ (𝟙 S) inferInstance))) := sorry

end AlgebraicGeometry.Scheme
