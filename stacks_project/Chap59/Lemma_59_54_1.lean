module

public import stacks_project.Chap59.Lemma_59_51_6_Presheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Acyclicity
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Opposite

noncomputable section

universe w u

namespace AlgebraicGeometry.Scheme

/- Lemma 59.54.1 (1): if `I` is injective on `X.Etale`, then positive Čech cohomology
of `f_* I` vanishes for every covering family of any `V` on `Y.Etale`. -/
@[stacks 03QB] #check
  (AlgebraicGeometry.Scheme.etalePushforward_cechCohomology_isZero_of_injective :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
      (V : Y.Etale) {ι : Type w} (𝒱 : ι → Over V)
      [HasFiniteProducts (Over V)] [HasProducts.{w} AddCommGrpCat.{u}]
      (h𝒱 : (Y.smallEtaleTopology.over V).CoversTop 𝒱) (p : ℕ) (hp : 0 < p),
      IsZero
        ((cechCohomologyOnSheaves Y.smallEtaleTopology 𝒱 p).obj
          ((AlgebraicGeometry.Scheme.etaleAbelianPushforward f).obj I)))

/- Lemma 59.54.1 (2): if `I` is injective on `X.Etale`, then `f_* I` is acyclic
for `Γ(V, -)` on `Y.Etale`. -/
@[stacks 03QB] #check
  (AlgebraicGeometry.Scheme.etalePushforward_sections_rightDerived_isZero_of_injective :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
      (V : Y.Etale)
      [Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [(siteAbelianSectionsFunctor Y.smallEtaleTopology V).Additive]
      (p : ℕ) (hp : 0 < p),
      IsZero
        (((siteAbelianSectionsFunctor Y.smallEtaleTopology V).rightDerived p).obj
          ((AlgebraicGeometry.Scheme.etaleAbelianPushforward f).obj I)))

/- Lemma 59.54.1 (3): if `I` is injective on `X.Etale` and `g : Y ⟶ Z`, then
`f_* I` is acyclic for `g_*`. -/
@[stacks 03QB] #check
  (AlgebraicGeometry.Scheme.etalePushforward_comp_rightDerived_isZero_of_injective :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
      (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective I]
      {Z : Scheme.{u}} (g : Y ⟶ Z)
      [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
      [Abelian (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
      [HasInjectiveResolutions (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
      [(AlgebraicGeometry.Scheme.etaleAbelianPushforward g).Additive]
      (p : ℕ) (hp : 0 < p),
      IsZero
        (((AlgebraicGeometry.Scheme.etaleAbelianPushforward g).rightDerived p).obj
          ((AlgebraicGeometry.Scheme.etaleAbelianPushforward f).obj I)))

end AlgebraicGeometry.Scheme
