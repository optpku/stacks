/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Sites.Continuous
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ConstantPullback

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The pullback map on small-étale cohomology of an arbitrary abelian sheaf along a
scheme morphism, landing in cohomology of the sheaf pullback on the source. -/
noncomputable def etaleHq_pullback {Z Z' : Scheme.{u}} (p : Z' ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ)
    [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify Z'.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u})]
    [((smallEtalePullback p).sheafPushforwardContinuous AddCommGrpCat.{u}
        Z.smallEtaleTopology Z'.smallEtaleTopology).IsRightAdjoint] :
    (Sheaf.functorH Z.smallEtaleTopology q).obj F ⟶
      (Sheaf.functorH Z'.smallEtaleTopology q).obj ((etaleAbelianSheafPullback p).obj F) :=
  AddCommGrpCat.ofHom
      ((etaleAbelianSheafPullback p).mapExtAddHom
        ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ)))
        F q) ≫
    AddCommGrpCat.ofHom
      (((Abelian.extFunctor q).map
          (inv (constantSheaf_sheafPullback_hom p (AddCommGrpCat.of (ULift ℤ)))).op).app
        ((etaleAbelianSheafPullback p).obj F)).hom

/-- The pullback map on small-étale cohomology of an abelian sheaf sends zero to zero. -/
theorem etaleHq_pullback_map_zero {Z Z' : Scheme.{u}} (p : Z' ⟶ Z)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ)
    [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [HasSheafify Z'.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf Z'.smallEtaleTopology AddCommGrpCat.{u})]
    [((smallEtalePullback p).sheafPushforwardContinuous AddCommGrpCat.{u}
        Z.smallEtaleTopology Z'.smallEtaleTopology).IsRightAdjoint] :
    etaleHq_pullback p F q 0 = 0 := sorry

/-- Identification of abelian-sheaf pullback with the identity induced by a natural
isomorphism `𝟭 X.Etale ≅ smallEtalePullback g`. -/
noncomputable def etaleAbelianSheafPullbackIso {X : Scheme.{u}} {g : X ⟶ X}
    (η : 𝟭 X.Etale ≅ smallEtalePullback g) :
    etaleAbelianSheafPullback g ≅ 𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  Adjunction.leftAdjointUniq
    ((smallEtalePullback g).sheafAdjunctionContinuous AddCommGrpCat.{u}
      X.smallEtaleTopology X.smallEtaleTopology)
    (Adjunction.id.ofNatIsoRight
      (Functor.sheafPushforwardContinuousId' η.symm
        AddCommGrpCat.{u} X.smallEtaleTopology).symm)

/-- The component of the coefficient identification at an abelian sheaf is a morphism
`(etaleAbelianSheafPullback g).obj F ⟶ F`. -/
noncomputable def etaleAbelianSheafPullbackIso_hom_app {X : Scheme.{u}} {g : X ⟶ X}
    (η : 𝟭 X.Etale ≅ smallEtalePullback g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianSheafPullback g).obj F ⟶ F :=
  (etaleAbelianSheafPullbackIso η).hom.app F

/-- The cohomology endomorphism obtained by pullback followed by the coefficient
identification induced by `𝟭 X.Etale ≅ smallEtalePullback g`. -/
noncomputable def etaleHq_ofSmallEtalePullbackIso {X : Scheme.{u}} (g : X ⟶ X)
    (η : 𝟭 X.Etale ≅ smallEtalePullback g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ) :
    (Sheaf.functorH X.smallEtaleTopology j).obj F ⟶
      (Sheaf.functorH X.smallEtaleTopology j).obj F :=
  etaleHq_pullback g F j ≫
    (Sheaf.functorH X.smallEtaleTopology j).map ((etaleAbelianSheafPullbackIso η).hom.app F)

/-- The induced cohomology endomorphism is pullback followed by the map on cohomology
of the coefficient identification. -/
theorem etaleHq_ofSmallEtalePullbackIso_spec {X : Scheme.{u}} (g : X ⟶ X)
    (η : 𝟭 X.Etale ≅ smallEtalePullback g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ) :
    etaleHq_ofSmallEtalePullbackIso g η F j =
      etaleHq_pullback g F j ≫
        (Sheaf.functorH X.smallEtaleTopology j).map
          ((etaleAbelianSheafPullbackIso η).hom.app F) := sorry

/-- A component of a small-étale pullback isomorphism commutes with the structure
morphisms to the base scheme. -/
theorem smallEtalePullbackIso_snd {X : Scheme.{u}} {g : X ⟶ X}
    (η : 𝟭 X.Etale ≅ smallEtalePullback g) (U : X.Etale) :
    (η.hom.app U).left ≫ pullback.snd U.hom g = U.hom := sorry

/-- A scheme self-map whose small-étale pullback is naturally isomorphic to the
identity induces the identity on cohomology of every abelian sheaf. -/
theorem etaleHq_ofSmallEtalePullbackIso_eq_id {X : Scheme.{u}} (g : X ⟶ X)
    (η : 𝟭 X.Etale ≅ smallEtalePullback g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ) :
    etaleHq_ofSmallEtalePullbackIso g η F j = 𝟙 _ := sorry

/-- The cohomology endomorphism induced by a small-étale pullback isomorphism fixes
every cohomology class. -/
theorem etaleHq_ofSmallEtalePullbackIso_apply {X : Scheme.{u}} (g : X ⟶ X)
    (η : 𝟭 X.Etale ≅ smallEtalePullback g)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ)
    (ξ : (Sheaf.functorH X.smallEtaleTopology j).obj F) :
    etaleHq_ofSmallEtalePullbackIso g η F j ξ = ξ := sorry

/-- A scheme self-map whose small-étale pullback is naturally isomorphic to the
identity induces the identity on cohomology with constant abelian coefficients. -/
theorem etaleHq_constant_pullback_eq_id_of_smallEtalePullbackIso {X : Scheme.{u}}
    (g : X ⟶ X) (η : 𝟭 X.Etale ≅ smallEtalePullback g)
    (M : AddCommGrpCat.{u}) (j : ℕ) :
    etaleHq_constant_pullback g M j = 𝟙 _ := sorry

end AlgebraicGeometry.Scheme.Hom
