/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseImageStalk
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousLeftAdjoint
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Products

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.GrothendieckTopology.Point

universe u

@[expose] public section

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasCoproducts.{u} AddCommGrpCat.{u}]
variable [HasProducts.{u} AddCommGrpCat.{u}]
variable [HasColimitsOfSize.{u, u} AddCommGrpCat.{u}]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback j).op.HasLeftKanExtension P]
variable [((smallEtalePullback j).sheafPushforwardContinuous AddCommGrpCat.{u}
    X.smallEtaleTopology U.smallEtaleTopology).IsRightAdjoint]

/-- The source coproduct of abelian stalks of `F` at geometric points of `U`
lifting a geometric point `xbar` of `X` along `j`. -/
noncomputable abbrev abelianExtensionByZero_stalkCoproduct
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (xbar : GeometricPoint X) :
    AddCommGrpCat.{u} :=
  ∐ fun u : GeometricPoint.Fiber j xbar ↦
    (GeometricPoint.toSmallEtalePoint u.point).sheafFiber.obj F

/-- Abelian form of the comap-to-image stalk comparison along étale `j`. -/
noncomputable def abelianEtaleInverseImage_comapFiberIso
    (ubar : GeometricPoint U)
    [InitiallySmall
      ((smallEtalePullback j ⋙ (GeometricPoint.toSmallEtalePoint ubar).fiber).Elements)]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((GeometricPoint.toSmallEtalePoint ubar).comapOfMorphismOfSites
        (smallEtalePullback j)).sheafFiber.obj G ≅
    (GeometricPoint.toSmallEtalePoint
          (@GeometricPoint.of X ubar.K inferInstance ubar.isAlgClosed
            (ubar.hom ≫ j))).sheafFiber.obj G :=
  { hom :=
      (Hom.sheafFiber ⟨smallEtaleInverseImage_comapFiberHom j ubar⟩).app G
    inv :=
      (Hom.sheafFiber ⟨smallEtaleInverseImage_comapFiberInv j ubar⟩).app G
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- The forward map of the comap-to-image stalk comparison is induced by the
comap fibre map. -/
theorem abelianEtaleInverseImage_comapFiberIso_hom
    (ubar : GeometricPoint U)
    [InitiallySmall
      ((smallEtalePullback j ⋙ (GeometricPoint.toSmallEtalePoint ubar).fiber).Elements)]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianEtaleInverseImage_comapFiberIso j ubar G).hom =
      (Hom.sheafFiber
        ⟨smallEtaleInverseImage_comapFiberHom j ubar⟩).app G :=
  sorry

/-- The inverse-image stalk is identified with the stalk at the composite
geometric point. -/
noncomputable def abelianEtaleInverseImage_stalkIso
    (ubar : GeometricPoint U)
    [InitiallySmall
      ((smallEtalePullback j ⋙ (GeometricPoint.toSmallEtalePoint ubar).fiber).Elements)]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (GeometricPoint.toSmallEtalePoint ubar).sheafFiber.obj
        (((smallEtalePullback j).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology U.smallEtaleTopology).obj G) ≅
      (GeometricPoint.toSmallEtalePoint
          (@GeometricPoint.of X ubar.K inferInstance ubar.isAlgClosed
            (ubar.hom ≫ j))).sheafFiber.obj G :=
  ((GeometricPoint.toSmallEtalePoint ubar).sheafFiberComapIsoOfMorphismOfSites
        (smallEtalePullback j) AddCommGrpCat.{u}).symm.app G ≪≫
    abelianEtaleInverseImage_comapFiberIso j ubar G

/-- The over-category comparison induced by `Fiber.point_comp`. -/
noncomputable def abelianEtaleInverseImage_fiberFiberOverIso
    (xbar : GeometricPoint X) (u : GeometricPoint.Fiber j xbar) :
    Over.mk (u.point.hom ≫ j) ≅ Over.mk xbar.hom :=
  Over.isoMk (Iso.refl _) (GeometricPoint.Fiber.point_comp u).symm

/-- The fibre map induced by `Fiber.point_comp`. -/
noncomputable def abelianEtaleInverseImage_fiberFiberHom
    (xbar : GeometricPoint X) (u : GeometricPoint.Fiber j xbar) :
    (GeometricPoint.toSmallEtalePoint
        (@GeometricPoint.of X u.point.K inferInstance u.point.isAlgClosed
          (u.point.hom ≫ j))).fiber ⟶
      (GeometricPoint.toSmallEtalePoint xbar).fiber where
  app V :=
    TypeCat.ofHom fun α ↦
      (abelianEtaleInverseImage_fiberFiberOverIso j xbar u).inv ≫ α
  naturality := fun _ _ _ ↦ sorry

/-- The inverse fibre map induced by `Fiber.point_comp`. -/
noncomputable def abelianEtaleInverseImage_fiberFiberInv
    (xbar : GeometricPoint X) (u : GeometricPoint.Fiber j xbar) :
    (GeometricPoint.toSmallEtalePoint xbar).fiber ⟶
      (GeometricPoint.toSmallEtalePoint
        (@GeometricPoint.of X u.point.K inferInstance u.point.isAlgClosed
          (u.point.hom ≫ j))).fiber where
  app V :=
    TypeCat.ofHom fun α ↦
      (abelianEtaleInverseImage_fiberFiberOverIso j xbar u).hom ≫ α
  naturality := fun _ _ _ ↦ sorry

/-- The fibre transport induced by the chosen geometric lift. -/
noncomputable def abelianEtaleInverseImage_fiberFiberIso
    (xbar : GeometricPoint X) (u : GeometricPoint.Fiber j xbar)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (GeometricPoint.toSmallEtalePoint
        (@GeometricPoint.of X u.point.K inferInstance u.point.isAlgClosed
          (u.point.hom ≫ j))).sheafFiber.obj G ≅
      (GeometricPoint.toSmallEtalePoint xbar).sheafFiber.obj G where
  hom :=
    (Hom.sheafFiber ⟨abelianEtaleInverseImage_fiberFiberHom j xbar u⟩).app G
  inv :=
    (Hom.sheafFiber ⟨abelianEtaleInverseImage_fiberFiberInv j xbar u⟩).app G
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of the fibre transport is induced by the fibre map. -/
theorem abelianEtaleInverseImage_fiberFiberIso_hom
    (xbar : GeometricPoint X) (u : GeometricPoint.Fiber j xbar)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianEtaleInverseImage_fiberFiberIso j xbar u G).hom =
      (Hom.sheafFiber
        ⟨abelianEtaleInverseImage_fiberFiberHom j xbar u⟩).app G :=
  sorry

/-- Transport the inverse-image stalk identification along `Fiber.point_comp`,
so the geometric point of `X` is the given `xbar`. -/
noncomputable def abelianEtaleInverseImage_stalkIso_fiber
    (xbar : GeometricPoint X) (u : GeometricPoint.Fiber j xbar)
    [InitiallySmall
      ((smallEtalePullback j ⋙
        (GeometricPoint.toSmallEtalePoint u.point).fiber).Elements)]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (GeometricPoint.toSmallEtalePoint u.point).sheafFiber.obj
        (((smallEtalePullback j).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology U.smallEtaleTopology).obj G) ≅
  (GeometricPoint.toSmallEtalePoint xbar).sheafFiber.obj G :=
  abelianEtaleInverseImage_stalkIso j u.point G ≪≫
    abelianEtaleInverseImage_fiberFiberIso j xbar u G

/-- Restriction of abelian étale sheaves along étale `j` is canonically
isomorphic to the chosen small étale inverse image. -/
noncomputable def etaleRestrictionSheafIso_smallEtalePullback
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleRestrictionSheaf j AddCommGrpCat.{u}).obj G ≅
      ((smallEtalePullback j).sheafPullback AddCommGrpCat.{u}
        X.smallEtaleTopology U.smallEtaleTopology).obj G :=
  (Functor.isoWhiskerLeft (etaleRestrictionSheaf j AddCommGrpCat.{u})
      (sheafificationNatIso U.smallEtaleTopology AddCommGrpCat.{u}) ≪≫
    Functor.isoWhiskerRight
      ((etaleRestriction j).sheafPushforwardContinuousCompSheafToPresheafIso
        AddCommGrpCat.{u} U.smallEtaleTopology X.smallEtaleTopology)
      (presheafToSheaf U.smallEtaleTopology AddCommGrpCat.{u})).app G ≪≫
    (Functor.LeftAdjoint.pullbackIsoCocontinuous
      (smallEtalePullback j) (etaleRestriction j)
      (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
        (inferInstance : Etale j) trivial)
      AddCommGrpCat.{u}).symm.app G

/-- The restriction-to-pullback comparison is the composite of its two
canonical natural-isomorphism components. -/
theorem etaleRestrictionSheafIso_smallEtalePullback_hom
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleRestrictionSheafIso_smallEtalePullback j G).hom =
      ((Functor.isoWhiskerLeft (etaleRestrictionSheaf j AddCommGrpCat.{u})
          (sheafificationNatIso U.smallEtaleTopology AddCommGrpCat.{u}) ≪≫
        Functor.isoWhiskerRight
          ((etaleRestriction j).sheafPushforwardContinuousCompSheafToPresheafIso
            AddCommGrpCat.{u} U.smallEtaleTopology X.smallEtaleTopology)
          (presheafToSheaf U.smallEtaleTopology AddCommGrpCat.{u})).app G ≪≫
        (Functor.LeftAdjoint.pullbackIsoCocontinuous
          (smallEtalePullback j) (etaleRestriction j)
          (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
            (inferInstance : Etale j) trivial)
          AddCommGrpCat.{u}).symm.app G).hom :=
  sorry

/-- The cocone leg from the stalk of `F` at a lift `u` of `xbar` to the
extension-by-zero stalk. -/
noncomputable def abelianExtensionByZero_stalkι
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (xbar : GeometricPoint X) (u : GeometricPoint.Fiber j xbar)
    [InitiallySmall
      ((smallEtalePullback j ⋙
        (GeometricPoint.toSmallEtalePoint u.point).fiber).Elements)] :
    (GeometricPoint.toSmallEtalePoint u.point).sheafFiber.obj F ⟶
      (GeometricPoint.toSmallEtalePoint xbar).sheafFiber.obj
        ((abelianExtensionByZero j).obj F) :=
  (GeometricPoint.toSmallEtalePoint u.point).sheafFiber.map
      ((abelianExtensionByZero_adjunction j).unit.app F) ≫
    (GeometricPoint.toSmallEtalePoint u.point).sheafFiber.map
      ((etaleRestrictionSheafIso_smallEtalePullback j
        ((abelianExtensionByZero j).obj F)).hom) ≫
    (abelianEtaleInverseImage_stalkIso_fiber j xbar u
      ((abelianExtensionByZero j).obj F)).hom

/-- The comparison morphism from the coproduct of source stalks to the
extension-by-zero stalk. -/
noncomputable def abelianExtensionByZero_stalkComparison
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (xbar : GeometricPoint X)
    [∀ u : GeometricPoint.Fiber j xbar,
      InitiallySmall
        ((smallEtalePullback j ⋙
          (GeometricPoint.toSmallEtalePoint u.point).fiber).Elements)] :
    abelianExtensionByZero_stalkCoproduct j F xbar ⟶
      (GeometricPoint.toSmallEtalePoint xbar).sheafFiber.obj
        ((abelianExtensionByZero j).obj F) :=
  Sigma.desc fun u : GeometricPoint.Fiber j xbar ↦
    abelianExtensionByZero_stalkι j F xbar u

/-- The comparison morphism is invertible for every abelian étale sheaf and
geometric point. -/
theorem abelianExtensionByZero_stalkIso
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (xbar : GeometricPoint X)
    [∀ u : GeometricPoint.Fiber j xbar,
      InitiallySmall
        ((smallEtalePullback j ⋙
          (GeometricPoint.toSmallEtalePoint u.point).fiber).Elements)] :
    IsIso (abelianExtensionByZero_stalkComparison j F xbar) :=
  sorry

/-- Extension by zero along an étale morphism is an exact functor on sheaves
of abelian groups. -/
theorem abelianExtensionByZero_exact :
    exactFunctor
      (Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (abelianExtensionByZero j) :=
  sorry

end AlgebraicGeometry.Scheme
