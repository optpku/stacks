/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AdditiveAdjunction

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain.ExactFirst
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Right
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.MorphismComparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.AbelianRestriction

/-!
# Derived comparison of big versus small étale pushforward

A morphism of algebraic stacks represented by algebraic spaces induces a
canonical identification of unbounded derived pushforwards after restriction
to the small étale sites, for abelian sheaves and for étale modules.
-/

@[expose] public section

-- Public constructions retain private implementation terms in their definitions.
set_option backward.privateInPublic true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ComplexShape
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Functor
open CategoryTheory.Sheaf.InternalModule
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Associated étale topologies admit abelian-group-valued sheaf composition with the
forgetful functor. -/
instance etaleTopology_hasSheafCompose_forget_addCommGrpCat (Z : GroupoidsOver S) :
    Z.etaleTopology.HasSheafCompose (forget AddCommGrpCat.{u}) :=
  sorry

/-- Small étale topologies of algebraic spaces admit abelian-group-valued sheaf composition
with the forgetful functor. -/
instance smallEtaleTopology_hasSheafCompose_forget_addCommGrpCat (A : AlgebraicSpace S) :
    (AlgebraicSpace.smallEtaleTopology A).HasSheafCompose (forget AddCommGrpCat.{u}) :=
  sorry

/-- Spaces étale topologies of algebraic spaces admit abelian-group-valued sheaf composition
with the forgetful functor. -/
instance spacesEtaleTopology_hasSheafCompose_forget_addCommGrpCat (A : AlgebraicSpace S) :
    (AlgebraicSpace.spacesEtaleTopology A).HasSheafCompose (forget AddCommGrpCat.{u}) :=
  sorry

/-- Direct image of abelian sheaves along a morphism of algebraic spaces is additive. -/
instance smallAbelianPushforward_additive {A B : AlgebraicSpace S} (h : A ⟶ B) :
    (AlgebraicSpace.EtaleAdditive.directImage h).Additive :=
  sorry

/-- Restriction of abelian étale sheaves along a representing algebraic space preserves
finite limits. -/
instance restrictAbelian.instPreservesFiniteLimits
    {A : AlgebraicSpace S} {Z : GroupoidsOver S} (e : A.toGroupoids ≌ Z) :
    PreservesFiniteLimits (restrictAbelian e) :=
  sorry

/-- Restriction of abelian étale sheaves along a representing algebraic space preserves
finite colimits. -/
instance restrictAbelian.instPreservesFiniteColimits
    {A : AlgebraicSpace S} {Z : GroupoidsOver S} (e : A.toGroupoids ≌ Z) :
    PreservesFiniteColimits (restrictAbelian e) :=
  sorry

/-- Direct image of abelian étale sheaves along a 1-morphism of categories fibred in
groupoids. -/
abbrev etaleAbelianPushforward {X' Y' : GroupoidsOver S} (h : X' ⟶ Y')
    [∀ P : X'.totalᵒᵖ ⥤ AddCommGrpCat.{u},
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P] :
    Sheaf X'.etaleTopology AddCommGrpCat.{u} ⥤
      Sheaf Y'.etaleTopology AddCommGrpCat.{u} :=
  (toCartesianBasedFunctor h).toFunctor.sheafPushforwardCocontinuous AddCommGrpCat.{u}
    X'.etaleTopology Y'.etaleTopology


/-- Direct image of abelian étale sheaves along a 1-morphism is additive. -/
instance etaleAbelianPushforward.instAdditive {X' Y' : GroupoidsOver S} (h : X' ⟶ Y')
    [∀ P : X'.totalᵒᵖ ⥤ AddCommGrpCat.{u},
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P] :
    (etaleAbelianPushforward h).Additive :=
  sorry

variable {X Y : GroupoidsOver S} {F G : AlgebraicSpace S}
variable (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y)
variable (α : (f ≫ eY.symm.hom) ≅
    (eX.symm.hom ≫ AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY)))
variable [HasSmallCFGTypeSections (S := S) f]

variable [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G) AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.spacesEtaleTopology F) AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) (Type u)]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G) (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor F X eX).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor F X eX).op]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor G Y eY).op]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasLeftKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasLeftKanExtension P]
variable [∀ P : X.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : F.toGroupoids.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : F.toGroupoids.totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor f).toFunctor.op]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY))).toFunctor.op]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X.etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf Y.etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (AlgebraicSpace.smallEtaleTopology G) AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf Y.etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf (AlgebraicSpace.smallEtaleTopology G) AddCommGrpCat.{u})]

/-- Continuous sheaf pushforward of abelian groups forgets to continuous sheaf pushforward
of types. -/
private def restrictAbelianForgetIso :
    restrictAbelian eY ⋙
        sheafCompose (AlgebraicSpace.smallEtaleTopology G) (forget AddCommGrpCat.{u}) ≅
      sheafCompose Y.etaleTopology (forget AddCommGrpCat.{u}) ⋙
        (smallEtaleFunctor G Y eY).sheafPushforwardContinuous (Type u)
          (AlgebraicSpace.smallEtaleTopology G) Y.etaleTopology :=
  Functor.fullyFaithfulCancelRight
    (sheafToPresheaf (AlgebraicSpace.smallEtaleTopology G) (Type u))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl))

/-- Cocontinuous sheaf pushforward of abelian groups forgets to cocontinuous sheaf
pushforward of types. -/
private def etaleAbelianPushforwardForgetIso :
    etaleAbelianPushforward f ⋙ sheafCompose Y.etaleTopology (forget AddCommGrpCat.{u}) ≅
      sheafCompose X.etaleTopology (forget AddCommGrpCat.{u}) ⋙
        (toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous (Type u)
          X.etaleTopology Y.etaleTopology :=
  Functor.sheafPushforwardCocontinuous.compSheafComposeIso
    (toCartesianBasedFunctor f).toFunctor (forget AddCommGrpCat.{u})
    X.etaleTopology Y.etaleTopology

/-- The two constructed type-valued direct images are right adjoints of the same
continuous restriction; their comparison uses both actual adjunctions. -/
def etaleTypePushforwardSmallSectionsIso :
    (toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous (Type u)
        X.etaleTopology Y.etaleTopology ≅
      (etaleRingedToposHom f).toTopos.pushforward :=
  ((toCartesianBasedFunctor f).toFunctor.sheafAdjunctionCocontinuous (Type u)
    X.etaleTopology Y.etaleTopology).rightAdjointUniq
      ((toFunctor f).sheafPushforwardOfSmallSectionsAdjunction
        X.etaleTopology Y.etaleTopology)

/-- Forgetting abelian groups after the left-hand composite recovers type-valued
`π_{G,*} f_*`. -/
private def compareAbelian_leftForgetIso :
    etaleAbelianPushforward f ⋙ restrictAbelian eY ⋙
        sheafCompose (AlgebraicSpace.smallEtaleTopology G) (forget AddCommGrpCat.{u}) ≅
      sheafCompose X.etaleTopology (forget AddCommGrpCat.{u}) ⋙
        (RingedSite.ToposHom.comp (etaleRingedToposHom f)
            (piToposHom G Y eY)).toTopos.pushforward :=
  (Functor.associator (etaleAbelianPushforward f) (restrictAbelian eY)
      (sheafCompose (AlgebraicSpace.smallEtaleTopology G) (forget AddCommGrpCat.{u}))) ≪≫
    Functor.isoWhiskerLeft (etaleAbelianPushforward f) (restrictAbelianForgetIso eY) ≪≫
    (Functor.associator (etaleAbelianPushforward f)
        (sheafCompose Y.etaleTopology (forget AddCommGrpCat.{u}))
        ((smallEtaleFunctor G Y eY).sheafPushforwardContinuous (Type u)
          (AlgebraicSpace.smallEtaleTopology G) Y.etaleTopology)).symm ≪≫
    Functor.isoWhiskerRight (etaleAbelianPushforwardForgetIso f)
      ((smallEtaleFunctor G Y eY).sheafPushforwardContinuous (Type u)
        (AlgebraicSpace.smallEtaleTopology G) Y.etaleTopology) ≪≫
    Functor.associator
      (sheafCompose X.etaleTopology (forget AddCommGrpCat.{u}))
      ((toCartesianBasedFunctor f).toFunctor.sheafPushforwardCocontinuous (Type u)
        X.etaleTopology Y.etaleTopology)
      ((smallEtaleFunctor G Y eY).sheafPushforwardContinuous (Type u)
        (AlgebraicSpace.smallEtaleTopology G) Y.etaleTopology) ≪≫
    Functor.isoWhiskerLeft (sheafCompose X.etaleTopology (forget AddCommGrpCat.{u}))
      (Functor.isoWhiskerRight (etaleTypePushforwardSmallSectionsIso f)
        ((smallEtaleFunctor G Y eY).sheafPushforwardContinuous (Type u)
          (AlgebraicSpace.smallEtaleTopology G) Y.etaleTopology))

/-- Forgetting abelian groups after the right-hand composite recovers type-valued
`f_small,* π_{F,*}`. -/
private def compareAbelian_rightForgetIso :
    restrictAbelian eX ⋙ AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY) ⋙
        sheafCompose (AlgebraicSpace.smallEtaleTopology G) (forget AddCommGrpCat.{u}) ≅
      sheafCompose X.etaleTopology (forget AddCommGrpCat.{u}) ⋙
        (RingedSite.ToposHom.comp (piToposHom F X eX)
            (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY))).toTopos.pushforward :=
  (Functor.associator (restrictAbelian eX) (AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY))
      (sheafCompose (AlgebraicSpace.smallEtaleTopology G) (forget AddCommGrpCat.{u}))) ≪≫
    Functor.isoWhiskerLeft (restrictAbelian eX)
      (AlgebraicSpace.EtaleAdditive.directImageForgetIso (moduleComparisonSpaceMorphism f eX eY)) ≪≫
    (Functor.associator (restrictAbelian eX)
        (sheafCompose (AlgebraicSpace.smallEtaleTopology F) (forget AddCommGrpCat.{u}))
        (AlgebraicSpace.typePushforward (moduleComparisonSpaceMorphism f eX eY))).symm ≪≫
    Functor.isoWhiskerRight (restrictAbelianForgetIso eX)
      (AlgebraicSpace.typePushforward (moduleComparisonSpaceMorphism f eX eY)) ≪≫
    Functor.associator
      (sheafCompose X.etaleTopology (forget AddCommGrpCat.{u}))
      ((smallEtaleFunctor F X eX).sheafPushforwardContinuous (Type u)
        (AlgebraicSpace.smallEtaleTopology F) X.etaleTopology)
      (AlgebraicSpace.typePushforward (moduleComparisonSpaceMorphism f eX eY))

/-- Underlying type-valued identification of the two abelian composites. -/
private def compareAbelian_forget (ℱ : Sheaf X.etaleTopology AddCommGrpCat.{u}) :
    (sheafCompose (AlgebraicSpace.smallEtaleTopology G) (forget AddCommGrpCat.{u})).obj
        ((etaleAbelianPushforward f ⋙ restrictAbelian eY).obj ℱ) ≅
      (sheafCompose (AlgebraicSpace.smallEtaleTopology G) (forget AddCommGrpCat.{u})).obj
        ((restrictAbelian eX ⋙ AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY)).obj ℱ) :=
  (compareAbelian_leftForgetIso eY f).app ℱ ≪≫
    (compareMorphismIso eX eY f α).app
      ((sheafCompose X.etaleTopology (forget AddCommGrpCat.{u})).obj ℱ) ≪≫
    (compareAbelian_rightForgetIso eX eY f).symm.app ℱ

/-- Presheaf-level lift of `compareAbelian_forget` through forgetting abelian groups. -/
private def compareAbelian_objPresheaf (ℱ : Sheaf X.etaleTopology AddCommGrpCat.{u}) :
    ((etaleAbelianPushforward f ⋙ restrictAbelian eY).obj ℱ).obj ≅
      ((restrictAbelian eX ⋙ AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY)).obj ℱ).obj :=
  NatIso.ofComponents
    (fun V ↦
      let e := (((sheafToPresheaf (AlgebraicSpace.smallEtaleTopology G) (Type u)).mapIso
        (compareAbelian_forget eX eY f α ℱ)).app V)
      AddEquiv.toAddCommGrpIso
        { toFun := e.hom
          invFun := e.inv
          left_inv := e.hom_inv_id_apply
          right_inv := e.inv_hom_id_apply
          map_add' := sorry })
    sorry

/-- The sheaf identification obtained by lifting `compareAbelian_forget` through the
forgetful functor on coefficients. -/
private def compareAbelian_obj (ℱ : Sheaf X.etaleTopology AddCommGrpCat.{u}) :
    (etaleAbelianPushforward f ⋙ restrictAbelian eY).obj ℱ ≅
      (restrictAbelian eX ⋙ AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY)).obj ℱ where
  hom := CategoryTheory.ObjectProperty.homMk (compareAbelian_objPresheaf eX eY f α ℱ).hom
  inv := CategoryTheory.ObjectProperty.homMk (compareAbelian_objPresheaf eX eY f α ℱ).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underived identification `(f_* ℱ)|_{G_étale} ≅ f_small,* (ℱ|_{F_étale})` of abelian
étale sheaves. -/
def compareAbelian :
    etaleAbelianPushforward f ⋙ restrictAbelian eY ≅
      restrictAbelian eX ⋙ AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY) :=
  NatIso.ofComponents (fun ℱ ↦ compareAbelian_obj eX eY f α ℱ) sorry

/-- After forgetting abelian-group structure, `compareAbelian` recovers the type-valued
cell of `compareMorphism`. -/
theorem compareAbelian_eq (ℱ : Sheaf X.etaleTopology AddCommGrpCat.{u}) :
    (sheafCompose (AlgebraicSpace.smallEtaleTopology G) (forget AddCommGrpCat.{u})).map
        ((compareAbelian eX eY f α).hom.app ℱ) =
      (compareAbelian_leftForgetIso eY f).hom.app ℱ ≫
        (compareMorphismIso eX eY f α).hom.app
          ((sheafCompose X.etaleTopology (forget AddCommGrpCat.{u})).obj ℱ) ≫
        (compareAbelian_rightForgetIso eX eY f).inv.app ℱ :=
  sorry

variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (etaleAbelianPushforward f))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY)))
    (HomologicalComplex.quasiIso
      (Sheaf (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleAbelianPushforward f ⋙ restrictAbelian eY))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (restrictAbelian eX ⋙ AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY)))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]

/-- The cochain-level unit for exact postcomposition of derived pushforward by restriction. -/
private def compareMorphismCohomology_postcompUnit :
    RightDerived.Cochain.toDerived (etaleAbelianPushforward f ⋙ restrictAbelian eY) ⟶
      (DerivedCategory.Q : CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u})) ⋙
        (RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
          (restrictAbelian eY).mapDerivedCategory) :=
  (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleAbelianPushforward f ⋙ restrictAbelian eY)) (up ℤ)).symm
      (DerivedCategory.Q : CochainComplex
        (Sheaf (AlgebraicSpace.smallEtaleTopology G) AddCommGrpCat.{u}) ℤ ⥤
        DerivedCategory (Sheaf (AlgebraicSpace.smallEtaleTopology G) AddCommGrpCat.{u}))).hom ≫
    (Functor.associator
        ((etaleAbelianPushforward f).mapHomologicalComplex (up ℤ))
        ((restrictAbelian eY).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q : CochainComplex
          (Sheaf (AlgebraicSpace.smallEtaleTopology G) AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory (Sheaf (AlgebraicSpace.smallEtaleTopology G) AddCommGrpCat.{u}))).hom ≫
    (isoWhiskerLeft ((etaleAbelianPushforward f).mapHomologicalComplex (up ℤ))
      (restrictAbelian eY).mapDerivedCategoryFactors.symm).hom ≫
    (Functor.associator
        ((etaleAbelianPushforward f).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q : CochainComplex (Sheaf Y.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory (Sheaf Y.etaleTopology AddCommGrpCat.{u}))
        (restrictAbelian eY).mapDerivedCategory).inv ≫
    whiskerRight (RightDerived.Cochain.unit (etaleAbelianPushforward f))
      (restrictAbelian eY).mapDerivedCategory ≫
    (Functor.associator
        (DerivedCategory.Q : CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
          DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u}))
        (RightDerived.Cochain.functor (etaleAbelianPushforward f))
        (restrictAbelian eY).mapDerivedCategory).hom

/-- The comparison from `R(f_* ⋙ π_{G,*})` to `Rf_*` followed by exact restriction. -/
private def compareMorphismCohomology_postcomp :
    RightDerived.Cochain.functor (etaleAbelianPushforward f ⋙ restrictAbelian eY) ⟶
      RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
        (restrictAbelian eY).mapDerivedCategory :=
  (RightDerived.Cochain.functor (etaleAbelianPushforward f ⋙ restrictAbelian eY)).rightDerivedDesc
    (RightDerived.Cochain.unit (etaleAbelianPushforward f ⋙ restrictAbelian eY))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))
    (RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
      (restrictAbelian eY).mapDerivedCategory)
    (compareMorphismCohomology_postcompUnit eY f)

/-- Exact postcomposition of derived abelian pushforward by restriction is an isomorphism. -/
private instance compareMorphismCohomology_postcomp_isIso :
    IsIso (compareMorphismCohomology_postcomp eY f) :=
  sorry

/-- Exact postcomposition of `Rf_*` by restriction is a right-derived model of the
underived composite. -/
private instance compareMorphismCohomology_postcomp_isRightDerived :
    (RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
      (restrictAbelian eY).mapDerivedCategory).IsRightDerivedFunctor
      (compareMorphismCohomology_postcompUnit eY f)
      (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ)) :=
  sorry

/-- The reverse comparison from exact postcomposition of `Rf_*` by restriction to
`R(f_* ⋙ π_{G,*})`. -/
private def compareMorphismCohomology_postcompInv :
    RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
        (restrictAbelian eY).mapDerivedCategory ⟶
      RightDerived.Cochain.functor (etaleAbelianPushforward f ⋙ restrictAbelian eY) :=
  (RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
      (restrictAbelian eY).mapDerivedCategory).rightDerivedDesc
    (compareMorphismCohomology_postcompUnit eY f)
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))
    (RightDerived.Cochain.functor (etaleAbelianPushforward f ⋙ restrictAbelian eY))
    (RightDerived.Cochain.unit (etaleAbelianPushforward f ⋙ restrictAbelian eY))

/-- Derived functorial form of the underived abelian identification `compareAbelian`. -/
private def compareMorphismCohomology_mapNatIso :
    RightDerived.Cochain.functor (etaleAbelianPushforward f ⋙ restrictAbelian eY) ≅
      RightDerived.Cochain.functor
        (restrictAbelian eX ⋙ AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY)) :=
  Functor.RightDerived.mapNatIso
    (DerivedCategory.Q : CochainComplex (Sheaf X.etaleTopology AddCommGrpCat.{u}) ℤ ⥤
      DerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u}))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))
    (isoWhiskerRight (NatIso.mapHomologicalComplex (compareAbelian eX eY f α) (up ℤ))
      (DerivedCategory.Q : CochainComplex
        (Sheaf (AlgebraicSpace.smallEtaleTopology G) AddCommGrpCat.{u}) ℤ ⥤
        DerivedCategory (Sheaf (AlgebraicSpace.smallEtaleTopology G) AddCommGrpCat.{u})))

/-- The functorial derived identification
`(Rf_* -)|_{G_étale} ≅ Rf_small,* ((-)|_{F_étale})` on abelian étale sheaves. -/
def compareMorphismCohomologyIso :
    RightDerived.Cochain.functor (etaleAbelianPushforward f) ⋙
        (restrictAbelian eY).mapDerivedCategory ≅
      (restrictAbelian eX).mapDerivedCategory ⋙
        RightDerived.Cochain.functor (AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY)) where
  hom :=
    compareMorphismCohomology_postcompInv eY f ≫
      (compareMorphismCohomology_mapNatIso eX eY f α).hom ≫
      (RightDerived.Cochain.ExactFirst.iso ((⟨restrictAbelian eX,
            ⟨restrictAbelian.instPreservesFiniteLimits eX,
              restrictAbelian.instPreservesFiniteColimits eX⟩⟩ : _ ⥤ₑ _))
          (AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY))).inv
  inv :=
    (RightDerived.Cochain.ExactFirst.iso ((⟨restrictAbelian eX,
            ⟨restrictAbelian.instPreservesFiniteLimits eX,
              restrictAbelian.instPreservesFiniteColimits eX⟩⟩ : _ ⥤ₑ _))
        (AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY))).hom ≫
      (compareMorphismCohomology_mapNatIso eX eY f α).inv ≫
      compareMorphismCohomology_postcomp eY f
  hom_inv_id := sorry
  inv_hom_id := sorry


/-- Forgetting module structure after `π_{G,*} f_*` recovers type-valued `π_{G,*} f_*`. -/
private def compareModules_leftForgetIso :
    etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward ⋙
        ToInternal.underlying (AlgebraicSpace.ringedSite G).structureSheaf ≅
      ToInternal.underlying (etaleRingedSite X).structureSheaf ⋙
        (RingedSite.ToposHom.comp (etaleRingedToposHom f)
            (piToposHom G Y eY)).toTopos.pushforward :=
  RingedSite.ToposHom.ModulePushforward.compForgetIso
    (etaleRingedToposHom f) (piToposHom G Y eY)

/-- Forgetting module structure after `f_small,* π_{F,*}` recovers type-valued
`f_small,* π_{F,*}`. -/
private def compareModules_rightForgetIso :
    (piToposHom F X eX).modulePushforward ⋙
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward ⋙
        ToInternal.underlying (AlgebraicSpace.ringedSite G).structureSheaf ≅
      ToInternal.underlying (etaleRingedSite X).structureSheaf ⋙
        (RingedSite.ToposHom.comp (piToposHom F X eX)
            (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY))).toTopos.pushforward :=
  RingedSite.ToposHom.ModulePushforward.compForgetIso
    (piToposHom F X eX) (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY))

/-- Underlying type-valued identification of the two module composites. -/
private def compareModules_forget
    (ℳ : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (ToInternal.underlying (AlgebraicSpace.ringedSite G).structureSheaf).obj
        ((etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward).obj ℳ) ≅
      (ToInternal.underlying (AlgebraicSpace.ringedSite G).structureSheaf).obj
        (((piToposHom F X eX).modulePushforward ⋙
          (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward).obj ℳ) :=
  (compareModules_leftForgetIso eY f).app ℳ ≪≫
    (compareMorphismIso eX eY f α).app
      ((ToInternal.underlying (etaleRingedSite X).structureSheaf).obj ℳ) ≪≫
    (compareModules_rightForgetIso eX eY f).symm.app ℳ

/-- The sheaf-of-modules identification obtained by lifting `compareModules_forget`. -/
private def compareModules_obj
    (ℳ : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward).obj ℳ ≅
      ((piToposHom F X eX).modulePushforward ⋙
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward).obj ℳ where
  hom :=
    homOfUnderlying (AlgebraicSpace.ringedSite G).structureSheaf
      (compareModules_forget eX eY f α ℳ).hom sorry sorry
  inv :=
    homOfUnderlying (AlgebraicSpace.ringedSite G).structureSheaf
      (compareModules_forget eX eY f α ℳ).inv sorry sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underived identification `(f_* ℳ)|_{G_étale} ≅ f_small,* (ℳ|_{F_étale})` of étale
modules. -/
def compareModules :
    etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward ≅
      (piToposHom F X eX).modulePushforward ⋙
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward :=
  NatIso.ofComponents (fun ℳ ↦ compareModules_obj eX eY f α ℳ) sorry

/-- After forgetting module structure, `compareModules` recovers the type-valued cell of
`compareMorphism`. -/
theorem compareModules_eq
    (ℳ : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    (ToInternal.underlying (AlgebraicSpace.ringedSite G).structureSheaf).map
        ((compareModules eX eY f α).hom.app ℳ) =
      (compareModules_leftForgetIso eY f).hom.app ℳ ≫
        (compareMorphismIso eX eY f α).hom.app
          ((ToInternal.underlying (etaleRingedSite X).structureSheaf).obj ℳ) ≫
        (compareModules_rightForgetIso eX eY f).inv.app ℳ :=
  sorry

variable [X.etaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Y.etaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [(AlgebraicSpace.smallEtaleTopology F).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [(AlgebraicSpace.smallEtaleTopology G).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (AlgebraicSpace.ringedSite F).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (AlgebraicSpace.ringedSite G).structureSheaf)]
variable [HasDerivedCategory (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)]
variable [HasDerivedCategory (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf)]
variable [HasDerivedCategory (SheafOfModules.{u} (AlgebraicSpace.ringedSite F).structureSheaf)]
variable [HasDerivedCategory (SheafOfModules.{u} (AlgebraicSpace.ringedSite G).structureSheaf)]

/-- Direct image of étale modules along `f` is additive. -/
instance etaleModuleDirectImage.instAdditive :
    (etaleModuleDirectImage f).Additive :=
  (etaleRingedToposHom f).modulePushforward_additive

/-- Restriction of étale modules along a representing equivalence is additive. -/
instance piToposHom.modulePushforward.instAdditive :
    ((piToposHom F X eX).modulePushforward).Additive :=
  (piToposHom F X eX).modulePushforward_additive


/-- Direct image of étale modules along a morphism of algebraic spaces is additive. -/
instance ringedToposHom.modulePushforward.instAdditive {A B : AlgebraicSpace S} (h : A ⟶ B) :
    (AlgebraicSpace.ringedToposHom h).modulePushforward.Additive :=
  (AlgebraicSpace.ringedToposHom h).modulePushforward_additive

/-- Restriction of étale modules along a representing equivalence preserves finite limits. -/
instance piToposHom.modulePushforward.instPreservesFiniteLimits :
    PreservesFiniteLimits (piToposHom F X eX).modulePushforward :=
  sorry


/-- Restriction of étale modules along a representing equivalence preserves finite colimits. -/
instance piToposHom.modulePushforward.instPreservesFiniteColimits :
    PreservesFiniteColimits (piToposHom F X eX).modulePushforward :=
  sorry


variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (etaleModuleDirectImage f))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (AlgebraicSpace.ringedSite F).structureSheaf) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((piToposHom F X eX).modulePushforward ⋙
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]

/-- The cochain-level unit for exact postcomposition of derived module pushforward by
`π_{G,*}`. -/
private def compareMorphismCohomology_modules_postcompUnit :
    RightDerived.Cochain.toDerived
        (etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward) ⟶
      (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) ℤ ⥤
            DerivedCategory (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)) ⋙
        (RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
          ((piToposHom G Y eY).modulePushforward).mapDerivedCategory) :=
  (isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward))
        (up ℤ)).symm
      (DerivedCategory.Q :
        CochainComplex (SheafOfModules.{u} (AlgebraicSpace.ringedSite G).structureSheaf) ℤ ⥤
          DerivedCategory
            (SheafOfModules.{u} (AlgebraicSpace.ringedSite G).structureSheaf))).hom ≫
    (Functor.associator
        ((etaleModuleDirectImage f).mapHomologicalComplex (up ℤ))
        (((piToposHom G Y eY).modulePushforward).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u} (AlgebraicSpace.ringedSite G).structureSheaf) ℤ ⥤
            DerivedCategory
              (SheafOfModules.{u} (AlgebraicSpace.ringedSite G).structureSheaf))).hom ≫
    (isoWhiskerLeft ((etaleModuleDirectImage f).mapHomologicalComplex (up ℤ))
      ((piToposHom G Y eY).modulePushforward).mapDerivedCategoryFactors.symm).hom ≫
    (Functor.associator
        ((etaleModuleDirectImage f).mapHomologicalComplex (up ℤ))
        (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf) ℤ ⥤
            DerivedCategory (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf))
        ((piToposHom G Y eY).modulePushforward).mapDerivedCategory).inv ≫
    whiskerRight (RightDerived.Cochain.unit (etaleModuleDirectImage f))
      ((piToposHom G Y eY).modulePushforward).mapDerivedCategory ≫
    (Functor.associator
        (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) ℤ ⥤
            DerivedCategory (SheafOfModules.{u} (etaleRingedSite X).structureSheaf))
        (RightDerived.Cochain.functor (etaleModuleDirectImage f))
        ((piToposHom G Y eY).modulePushforward).mapDerivedCategory).hom

/-- The comparison from `R(f_* ⋙ π_{G,*})` to `Rf_*` followed by exact restriction of modules. -/
private def compareMorphismCohomology_modules_postcomp :
    RightDerived.Cochain.functor
        (etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward) ⟶
      RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
        ((piToposHom G Y eY).modulePushforward).mapDerivedCategory :=
  (RightDerived.Cochain.functor
      (etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward)).rightDerivedDesc
    (RightDerived.Cochain.unit
      (etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))
    (RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
      ((piToposHom G Y eY).modulePushforward).mapDerivedCategory)
    (compareMorphismCohomology_modules_postcompUnit eY f)

/-- Exact postcomposition of derived module pushforward by `π_{G,*}` is an isomorphism. -/
private instance compareMorphismCohomology_modules_postcomp_isIso :
    IsIso (compareMorphismCohomology_modules_postcomp eY f) :=
  sorry

/-- Exact postcomposition of `Rf_*` by `π_{G,*}` is a right-derived model of the
underived module composite. -/
private instance compareMorphismCohomology_modules_postcomp_isRightDerived :
    (RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
      ((piToposHom G Y eY).modulePushforward).mapDerivedCategory).IsRightDerivedFunctor
      (compareMorphismCohomology_modules_postcompUnit eY f)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ)) :=
  sorry

/-- The reverse comparison from exact postcomposition of `Rf_*` by `π_{G,*}` to
`R(f_* ⋙ π_{G,*})`. -/
private def compareMorphismCohomology_modules_postcompInv :
    RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
        ((piToposHom G Y eY).modulePushforward).mapDerivedCategory ⟶
      RightDerived.Cochain.functor
        (etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward) :=
  (RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
      ((piToposHom G Y eY).modulePushforward).mapDerivedCategory).rightDerivedDesc
    (compareMorphismCohomology_modules_postcompUnit eY f)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))
    (RightDerived.Cochain.functor
      (etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward))
    (RightDerived.Cochain.unit
      (etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward))

/-- The cochain-level unit for exact precomposition of derived small module pushforward by
`π_{F,*}`. -/
private def compareMorphismCohomology_modules_precompUnit :
    RightDerived.Cochain.toDerived
        ((piToposHom F X eX).modulePushforward ⋙
          (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward) ⟶
      (DerivedCategory.Q :
          CochainComplex (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) ℤ ⥤
            DerivedCategory (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)) ⋙
        (((piToposHom F X eX).modulePushforward).mapDerivedCategory ⋙
          RightDerived.Cochain.functor
            (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward) :=
  (RightDerived.Cochain.ExactFirst.toIteratedIso
      (ExactFunctor.of (piToposHom F X eX).modulePushforward)
      (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward).hom ≫
    RightDerived.Composition.iteratedUnit
      ((piToposHom F X eX).modulePushforward).mapDerivedCategoryFactors.inv
      (RightDerived.Cochain.unit
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward)

/-- The comparison from `R(π_{F,*} ⋙ f_small,*)` to exact restriction followed by
`Rf_small,*`. -/
private def compareMorphismCohomology_modules_precomp :
    RightDerived.Cochain.functor
        ((piToposHom F X eX).modulePushforward ⋙
          (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward) ⟶
      ((piToposHom F X eX).modulePushforward).mapDerivedCategory ⋙
        RightDerived.Cochain.functor
          (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward :=
  (RightDerived.Cochain.functor
      ((piToposHom F X eX).modulePushforward ⋙
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward)).rightDerivedDesc
    (RightDerived.Cochain.unit
      ((piToposHom F X eX).modulePushforward ⋙
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))
    (((piToposHom F X eX).modulePushforward).mapDerivedCategory ⋙
      RightDerived.Cochain.functor
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward)
    (compareMorphismCohomology_modules_precompUnit eX eY f)

/-- Exact precomposition of derived small module pushforward by `π_{F,*}` is an isomorphism. -/
private instance compareMorphismCohomology_modules_precomp_isIso :
    IsIso (compareMorphismCohomology_modules_precomp eX eY f) :=
  sorry

/-- Exact precomposition of `Rf_small,*` by `π_{F,*}` is a right-derived model of the
underived module composite, by the geometric composition law and exactness of restriction. -/
private instance compareMorphismCohomology_modules_precomp_isRightDerived :
    (((piToposHom F X eX).modulePushforward).mapDerivedCategory ⋙
      RightDerived.Cochain.functor
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward).IsRightDerivedFunctor
      (compareMorphismCohomology_modules_precompUnit eX eY f)
      (HomologicalComplex.quasiIso
        (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ)) :=
  sorry

/-- The reverse comparison from exact restriction followed by `Rf_small,*` to
`R(π_{F,*} ⋙ f_small,*)`. -/
private def compareMorphismCohomology_modules_precompInv :
    ((piToposHom F X eX).modulePushforward).mapDerivedCategory ⋙
        RightDerived.Cochain.functor
          (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward ⟶
      RightDerived.Cochain.functor
        ((piToposHom F X eX).modulePushforward ⋙
          (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward) :=
  (((piToposHom F X eX).modulePushforward).mapDerivedCategory ⋙
      RightDerived.Cochain.functor
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward).rightDerivedDesc
    (compareMorphismCohomology_modules_precompUnit eX eY f)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))
    (RightDerived.Cochain.functor
      ((piToposHom F X eX).modulePushforward ⋙
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward))
    (RightDerived.Cochain.unit
      ((piToposHom F X eX).modulePushforward ⋙
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward))

/-- Derived functorial form of the underived module identification `compareModules`. -/
private def compareMorphismCohomology_modules_mapNatIso :
    RightDerived.Cochain.functor
        (etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward) ≅
      RightDerived.Cochain.functor
        ((piToposHom F X eX).modulePushforward ⋙
          (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward) :=
  Functor.RightDerived.mapNatIso
    (DerivedCategory.Q :
      CochainComplex (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) ℤ ⥤
        DerivedCategory (SheafOfModules.{u} (etaleRingedSite X).structureSheaf))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))
    (isoWhiskerRight (NatIso.mapHomologicalComplex (compareModules eX eY f α) (up ℤ))
      (DerivedCategory.Q :
        CochainComplex (SheafOfModules.{u} (AlgebraicSpace.ringedSite G).structureSheaf) ℤ ⥤
          DerivedCategory
            (SheafOfModules.{u} (AlgebraicSpace.ringedSite G).structureSheaf)))

/-- The functorial derived identification
`(Rf_* -)|_{G_étale} ≅ Rf_small,* ((-)|_{F_étale})` on étale modules. -/
def compareMorphismCohomology_modulesIso :
    RightDerived.Cochain.functor (etaleModuleDirectImage f) ⋙
        ((piToposHom G Y eY).modulePushforward).mapDerivedCategory ≅
      ((piToposHom F X eX).modulePushforward).mapDerivedCategory ⋙
        RightDerived.Cochain.functor
          (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward where
  hom :=
    compareMorphismCohomology_modules_postcompInv eY f ≫
      (compareMorphismCohomology_modules_mapNatIso eX eY f α).hom ≫
      compareMorphismCohomology_modules_precomp eX eY f
  inv :=
    compareMorphismCohomology_modules_precompInv eX eY f ≫
      (compareMorphismCohomology_modules_mapNatIso eX eY f α).inv ≫
      compareMorphismCohomology_modules_postcomp eY f
  hom_inv_id := sorry
  inv_hom_id := sorry


end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The presentation equivalences identify a morphism with the map of groupoid fibrations
induced by its fiberwise evaluated morphism of algebraic spaces. -/
private def canonicalInducedTwoIso {X Y : GroupoidsOver S} {F G : AlgebraicSpace S}
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y) :
    (f ≫ eY.symm.hom) ≅
      (eX.symm.hom ≫ AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY)) := by
  let P := (eX.hom ≫ f) ≫ eY.inv
  let h := AlgebraicSpace.toGroupoids.eval P
  let b : toBasedFunctor P ≅ toBasedFunctor (AlgebraicSpace.toGroupoids.map h) :=
    BasedNatIso.ofComponents
      (fun a ↦
        { hom := (CategoryOfElements.homMk
            (Opposite.unop ((toFunctor (AlgebraicSpace.toGroupoids.map h)).obj a))
            (Opposite.unop ((toFunctor P).obj a))
            (((eqToIso (comm P)).hom.app a).op) sorry).op
          inv := (CategoryOfElements.homMk
            (Opposite.unop ((toFunctor P).obj a))
            (Opposite.unop ((toFunctor (AlgebraicSpace.toGroupoids.map h)).obj a))
            (((eqToIso (comm P)).inv.app a).op) sorry).op
          hom_inv_id := sorry
          inv_hom_id := sorry }) sorry sorry
  let β : P ≅ AlgebraicSpace.toGroupoids.map h := BasedFunctorIso.lift b
  exact (Bicategory.leftUnitor (f ≫ eY.inv)).symm ≪≫
    Bicategory.whiskerRightIso eX.counit.symm (f ≫ eY.inv) ≪≫
    Bicategory.associator eX.inv eX.hom (f ≫ eY.inv) ≪≫
    Bicategory.whiskerLeftIso eX.inv (Bicategory.associator eX.hom f eY.inv).symm ≪≫
    Bicategory.whiskerLeftIso eX.inv β

variable {X Y : GroupoidsOver S} {F G : AlgebraicSpace S}
variable (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y)
variable [AlgebraicStack X] [AlgebraicStack Y]
variable [HasSheafify X.etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.etaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G) AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.spacesEtaleTopology F) AddCommGrpCat.{u}]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology F) (Type u)]
variable [HasSheafify (AlgebraicSpace.smallEtaleTopology G) (Type u)]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor F X eX).op.HasPointwiseRightKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ RingCat.{u},
    (smallEtaleFunctor G Y eY).op.HasPointwiseRightKanExtension P]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor F X eX).op]
variable [(forget RingCat.{u}).PreservesRightKanExtensions (smallEtaleFunctor G Y eY).op]
variable [∀ P : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor F X eX).op.HasLeftKanExtension P]
variable [∀ P : (AlgebraicSpace.smallEtaleSite G)ᵒᵖ ⥤ Type u,
    (smallEtaleFunctor G Y eY).op.HasLeftKanExtension P]
variable [∀ P : X.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : F.toGroupoids.totalᵒᵖ ⥤ Type u,
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : X.totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [∀ P : F.toGroupoids.totalᵒᵖ ⥤ AddCommGrpCat.{u},
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY))).toFunctor.op.HasPointwiseRightKanExtension P]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor f).toFunctor.op]
variable [(forget AddCommGrpCat.{u}).PreservesRightKanExtensions
    (toCartesianBasedFunctor
        (AlgebraicSpace.toGroupoids.map (moduleComparisonSpaceMorphism f eX eY))).toFunctor.op]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X.etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf Y.etaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf (AlgebraicSpace.smallEtaleTopology G) AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X.etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf Y.etaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf (AlgebraicSpace.smallEtaleTopology G) AddCommGrpCat.{u})]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (etaleAbelianPushforward f))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY)))
    (HomologicalComplex.quasiIso
      (Sheaf (AlgebraicSpace.smallEtaleTopology F) AddCommGrpCat.{u}) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleAbelianPushforward f ⋙ restrictAbelian eY))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (restrictAbelian eX ⋙ AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY)))
    (HomologicalComplex.quasiIso (Sheaf X.etaleTopology AddCommGrpCat.{u}) (up ℤ))]
variable [X.etaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [Y.etaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [(AlgebraicSpace.smallEtaleTopology F).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [(AlgebraicSpace.smallEtaleTopology G).WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (AlgebraicSpace.ringedSite F).structureSheaf)]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (SheafOfModules.{u} (AlgebraicSpace.ringedSite G).structureSheaf)]
variable [HasDerivedCategory (SheafOfModules.{u} (etaleRingedSite X).structureSheaf)]
variable [HasDerivedCategory (SheafOfModules.{u} (etaleRingedSite Y).structureSheaf)]
variable [HasDerivedCategory (SheafOfModules.{u} (AlgebraicSpace.ringedSite F).structureSheaf)]
variable [HasDerivedCategory (SheafOfModules.{u} (AlgebraicSpace.ringedSite G).structureSheaf)]
-- Local instance justification (defeq pin): the explicit representing equivalences eX and eY select the small-section certificate used by etaleModuleDirectImage f and this derived-existence assumption; f alone cannot infer it.
variable [letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived (etaleModuleDirectImage f))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (AlgebraicSpace.ringedSite F).structureSheaf) (up ℤ))]
-- Local instance justification (defeq pin): the explicit representing equivalences eX and eY select the small-section certificate used by the composite module direct image and this derived-existence assumption; f alone cannot infer it.
variable [letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      (etaleModuleDirectImage f ⋙ (piToposHom G Y eY).modulePushforward))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]
variable [HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((piToposHom F X eX).modulePushforward ⋙
        (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward))
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) (up ℤ))]

/-- Derived direct image of an abelian étale sheaf commutes with restriction to the
small étale sites of representing algebraic spaces. -/
def compareMorphismCohomology (ℱ : Sheaf X.etaleTopology AddCommGrpCat.{u}) :
    -- Local instance justification (defeq pin): the explicit representing equivalences eX and eY select the small-section certificate needed to instantiate the abelian comparison; f alone cannot infer it.
    letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    ((restrictAbelian eY).mapDerivedCategory).obj
        ((RightDerived.Cochain.functor (etaleAbelianPushforward f)).obj
          ((DerivedCategory.singleFunctor
              (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0).obj ℱ)) ≅
      (RightDerived.Cochain.functor
          (AlgebraicSpace.EtaleAdditive.directImage (moduleComparisonSpaceMorphism f eX eY))).obj
        ((restrictAbelian eX).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor
              (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0).obj ℱ)) :=
  -- Local instance justification (defeq pin): the abelian comparison body must use the same presentation-selected small-section certificate as its conclusion; f alone cannot infer that certificate.
  letI := hasSmallCFGTypeSections_ofRepresented f eX eY
  (compareMorphismCohomologyIso eX eY f (canonicalInducedTwoIso eX eY f)).app
    ((DerivedCategory.singleFunctor (Sheaf X.etaleTopology AddCommGrpCat.{u}) 0).obj ℱ)

/-- Derived direct image of an étale structure-sheaf module commutes with restriction
to the small étale sites of representing algebraic spaces. -/
def compareMorphismCohomology_modules
    (ℳ : SheafOfModules.{u} (etaleRingedSite X).structureSheaf) :
    -- Local instance justification (defeq pin): the explicit representing equivalences eX and eY select the small-section certificate fixing etaleModuleDirectImage f in this conclusion and its derived-existence assumptions; f alone cannot infer it.
    letI := hasSmallCFGTypeSections_ofRepresented f eX eY
    (((piToposHom G Y eY).modulePushforward).mapDerivedCategory).obj
        ((RightDerived.Cochain.functor (etaleModuleDirectImage f)).obj
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0).obj ℳ)) ≅
      (RightDerived.Cochain.functor
          (AlgebraicSpace.ringedToposHom (moduleComparisonSpaceMorphism f eX eY)).modulePushforward).obj
        ((((piToposHom F X eX).modulePushforward).mapDerivedCategory).obj
          ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0).obj ℳ)) :=
  -- Local instance justification (defeq pin): the module comparison body must use the same presentation-selected small-section certificate as its conclusion and derived-existence assumptions; f alone cannot infer that certificate.
  letI := hasSmallCFGTypeSections_ofRepresented f eX eY
  (compareMorphismCohomology_modulesIso eX eY f (canonicalInducedTwoIso eX eY f)).app
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (etaleRingedSite X).structureSheaf) 0).obj ℳ)

end AlgebraicGeometry.GroupoidsOver

