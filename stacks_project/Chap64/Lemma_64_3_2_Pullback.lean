/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.PullbackIso

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Pullback on small-étale cohomology of an arbitrary abelian sheaf. -/
#check (AlgebraicGeometry.Scheme.Hom.etaleHq_pullback :
  ∀ {Z Z' : Scheme.{u}} (p : Z' ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ)
    [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify Z'.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u})]
    [((smallEtalePullback p).sheafPushforwardContinuous AddCommGrpCat.{u}
        Z.smallEtaleTopology Z'.smallEtaleTopology).IsRightAdjoint],
    (Sheaf.functorH Z.smallEtaleTopology q).obj F ⟶
      (Sheaf.functorH Z'.smallEtaleTopology q).obj ((etaleAbelianSheafPullback p).obj F))

/- Pullback sends zero to zero. -/
#check (AlgebraicGeometry.Scheme.Hom.etaleHq_pullback_map_zero :
  ∀ {Z Z' : Scheme.{u}} (p : Z' ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ)
    [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify Z'.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u})]
    [((smallEtalePullback p).sheafPushforwardContinuous AddCommGrpCat.{u}
        Z.smallEtaleTopology Z'.smallEtaleTopology).IsRightAdjoint],
    etaleHq_pullback p F q 0 = 0)

/- The natural isomorphism identifies coefficient pullback with the identity. -/
#check (AlgebraicGeometry.Scheme.Hom.etaleAbelianSheafPullbackIso :
  ∀ {X : Scheme.{u}} {g : X ⟶ X} (η : 𝟭 X.Etale ≅ smallEtalePullback g),
    etaleAbelianSheafPullback g ≅ 𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))

/- The coefficient identification has a component at every abelian sheaf. -/
#check (AlgebraicGeometry.Scheme.Hom.etaleAbelianSheafPullbackIso_hom_app :
  ∀ {X : Scheme.{u}} {g : X ⟶ X}
    (η : 𝟭 X.Etale ≅ smallEtalePullback g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}),
    (etaleAbelianSheafPullback g).obj F ⟶ F)

/- Pullback and coefficient identification induce a cohomology endomorphism. -/
#check (AlgebraicGeometry.Scheme.Hom.etaleHq_ofSmallEtalePullbackIso :
  ∀ {X : Scheme.{u}} (g : X ⟶ X)
    (η : 𝟭 X.Etale ≅ smallEtalePullback g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ),
    (Sheaf.functorH X.smallEtaleTopology j).obj F ⟶
      (Sheaf.functorH X.smallEtaleTopology j).obj F)

/- The cohomology endomorphism is the composite defining it. -/
#check (AlgebraicGeometry.Scheme.Hom.etaleHq_ofSmallEtalePullbackIso_spec :
  ∀ {X : Scheme.{u}} (g : X ⟶ X)
    (η : 𝟭 X.Etale ≅ smallEtalePullback g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ),
    etaleHq_ofSmallEtalePullbackIso g η F j =
      etaleHq_pullback g F j ≫
        (Sheaf.functorH X.smallEtaleTopology j).map
          ((etaleAbelianSheafPullbackIso η).hom.app F))

/- Each component commutes with the structure morphism to the base. -/
#check (AlgebraicGeometry.Scheme.Hom.smallEtalePullbackIso_snd :
  ∀ {X : Scheme.{u}} {g : X ⟶ X}
    (η : 𝟭 X.Etale ≅ smallEtalePullback g) (U : X.Etale),
    (η.hom.app U).left ≫ pullback.snd U.hom g = U.hom)

end AlgebraicGeometry.Scheme.Hom
