/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleSite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos
public import ReasLib.CategoryTheory.Sites.Simplicial.SheafSystem
public import ReasLib.CategoryTheory.Sites.Topos.TwoMorphism
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Total augmentations of simplicial étale sites -/

set_option backward.privateInPublic true

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.SimplicialSites
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- The étale topos morphism associated to a simplex operator. -/
private abbrev etaleStageMap {m n : SimplexCategory} (φ : m ⟶ n) :=
  spacesEtaleMorphismOfTopoi (U.map φ.op)

/-- Pullback along the identity simplex is canonically the identity site functor. -/
private def etaleStageId (n : SimplexCategory) :
    spacesEtalePullback (U.map (𝟙 n).op) ≅ 𝟭 (spacesEtaleSite (U.obj (op n))) :=
  let e : MorphismProperty.Over.map (P := @Etale S) ⊤
      (f := 𝟙 (U.obj (op n))) inferInstance ≅ 𝟭 (spacesEtaleSite (U.obj (op n))) :=
    NatIso.ofComponents
      (fun V ↦ MorphismProperty.Over.isoMk (Iso.refl _)
        (by change 𝟙 V.left ≫ V.hom = V.hom ≫ 𝟙 _; simp))
      (by intro V W f; ext; change f.left ≫ 𝟙 W.left = 𝟙 V.left ≫ f.left; simp)
  MorphismProperty.Over.pullbackCongr (by simpa using U.map_id (op n)) ≪≫
    ((MorphismProperty.Over.mapPullbackAdj (@Etale S) ⊤ (𝟙 (U.obj (op n)))
      inferInstance trivial).ofNatIsoLeft e).rightAdjointUniq Adjunction.id

/-- Composition of simplex operators induces the canonical base-change comparison. -/
private def etaleStageComp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    spacesEtalePullback (U.map ψ.op) ⋙ spacesEtalePullback (U.map φ.op) ≅
      spacesEtalePullback (U.map (ψ ≫ φ).op) :=
  (spacesEtalePullbackComp (U.map φ.op) (U.map ψ.op)).symm ≪≫
    MorphismProperty.Over.pullbackCongr (by simpa using (U.map_comp φ.op ψ.op).symm)

/-- Stage direct images have their canonical identity and composition comparisons. -/
private instance etaleStageFunctoriality :
    HasPushforwardFunctoriality
      (fun n : SimplexCategory ↦ spacesEtaleTopology (U.obj (op n)))
      (fun φ ↦ etaleStageMap U φ) where
  pushforwardIdIso n :=
    Functor.sheafPushforwardContinuousId' (etaleStageId U n) (Type (u + 1))
      (spacesEtaleTopology (U.obj (op n)))
  pushforwardCompIso ψ φ :=
    Functor.sheafPushforwardContinuousComp' (etaleStageComp U ψ φ) (Type (u + 1))
      (spacesEtaleTopology (U.obj (op _)))
      (spacesEtaleTopology (U.obj (op _)))
      (spacesEtaleTopology (U.obj (op _)))

/-- Systems of stage étale sheaves with transitions along the simplicial structure maps. -/
private abbrev EtaleSystem :=
  SheafSystem (fun n : SimplexCategory ↦ spacesEtaleTopology (U.obj (op n)))
    (fun φ ↦ etaleStageMap U φ)

/-- Restriction of a total presheaf to a stage. -/
private def etaleRestrictionPresheaf (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)))
    (n : SimplexCategory) := (SpacesEtale.includeStage (U := U) (op n)).op ⋙ F.obj

/-- Stage restrictions of total sheaves satisfy the sheaf condition. -/
private abbrev etaleRestrictionSheafLaw :=
  ∀ (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))) (n : SimplexCategory),
    Presheaf.IsSheaf (spacesEtaleTopology (U.obj (op n))) (etaleRestrictionPresheaf U F n)

/-- Restriction to a stage, with its sheaf-condition proof displayed. -/
private def etaleRestriction (h : etaleRestrictionSheafLaw U) (n : SimplexCategory) :
    Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)) ⥤
      Sheaf (spacesEtaleTopology (U.obj (op n))) (Type (u + 1)) where
  obj F := ⟨etaleRestrictionPresheaf U F n, h F n⟩
  map α := ObjectProperty.homMk
    { app := fun V ↦ α.hom.app ((SpacesEtale.includeStage (U := U) (op n)).op.obj V)
      naturality := by intro V W f; exact α.hom.naturality _ }
  map_id := by intro F; ext V x; rfl
  map_comp := by intro F G H α β; ext V x; rfl

/-- Transition on sections is restriction along the canonical cartesian square. -/
private def toEtaleTransitionApp (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)))
    {m n : SimplexCategory} (φ : m ⟶ n) (V : (spacesEtaleSite (U.obj (op m)))ᵒᵖ) :=
  F.obj.map (SpacesEtale.homEquivFromPullback
    (Y := (SpacesEtale.ofStage (op n) ((spacesEtalePullback (U.map φ.op)).obj V.unop) : SpacesEtale U))
    (Z := (SpacesEtale.ofStage (op m) V.unop : SpacesEtale U)) φ (𝟙 _)).op

/-- Section transitions commute with restrictions within a stage. -/
private abbrev toEtaleTransitionLaw :=
  ∀ (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)))
    {m n : SimplexCategory} (φ : m ⟶ n)
    {V W : (spacesEtaleSite (U.obj (op m)))ᵒᵖ} (η : V ⟶ W),
    (etaleRestrictionPresheaf U F m).map η ≫ toEtaleTransitionApp U F φ W =
      toEtaleTransitionApp U F φ V ≫
        (etaleRestrictionPresheaf U F n).map ((spacesEtalePullback (U.map φ.op)).op.map η)

/-- Stage transitions as maps to direct images. -/
private def toEtaleTransition (hs : etaleRestrictionSheafLaw U)
    (hn : toEtaleTransitionLaw U)
    (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (etaleRestriction U hs m).obj F ⟶
      (etaleStageMap U φ).pushforward.obj ((etaleRestriction U hs n).obj F) :=
  ObjectProperty.homMk
    { app := toEtaleTransitionApp U F φ
      naturality := fun _ _ η ↦ hn F φ η }

/-- Restriction and cartesian-square transitions define a functor to stage sheaf systems. -/
private theorem toEtaleSheafSystem_laws :
    etaleRestrictionSheafLaw U ∧ toEtaleTransitionLaw U ∧
    ∀ (hs : etaleRestrictionSheafLaw U) (hn : toEtaleTransitionLaw U),
    (∀ (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))) (n : SimplexCategory),
      toEtaleTransition U hs hn F (𝟙 n) =
        (HasPushforwardFunctoriality.pushforwardIdIso (fHom := fun φ ↦ etaleStageMap U φ) n).inv.app
          ((etaleRestriction U hs n).obj F)) ∧
    (∀ (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)))
      {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      toEtaleTransition U hs hn F (ψ ≫ φ) =
        toEtaleTransition U hs hn F ψ ≫ (etaleStageMap U ψ).pushforward.map
          (toEtaleTransition U hs hn F φ) ≫
        (HasPushforwardFunctoriality.pushforwardCompIso (fHom := fun φ ↦ etaleStageMap U φ) ψ φ).hom.app
          ((etaleRestriction U hs n).obj F)) ∧
    (∀ {F G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))} (α : F ⟶ G)
      {m n : SimplexCategory} (φ : m ⟶ n),
      toEtaleTransition U hs hn F φ ≫ (etaleStageMap U φ).pushforward.map
        ((etaleRestriction U hs n).map α) =
      (etaleRestriction U hs m).map α ≫ toEtaleTransition U hs hn G φ) :=
  sorry

/-- The sheaf system obtained by restricting a total étale sheaf to every stage. -/
def toEtaleSheafSystem :
    Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)) ⥤ EtaleSystem U where
  obj F := SheafSystem.of
    (fun n ↦ (etaleRestriction U (toEtaleSheafSystem_laws U).1 n).obj F)
    (fun φ ↦ toEtaleTransition U (toEtaleSheafSystem_laws U).1 (toEtaleSheafSystem_laws U).2.1 F φ)
    (((toEtaleSheafSystem_laws U).2.2 _ _).1 F)
    (((toEtaleSheafSystem_laws U).2.2 _ _).2.1 F)
  map α := SheafSystem.homMk
    (fun n ↦ (etaleRestriction U (toEtaleSheafSystem_laws U).1 n).map α)
    (((toEtaleSheafSystem_laws U).2.2 _ _).2.2 α)
  map_id := by intro F; apply SheafSystem.Hom.ext; intro n; ext V x; rfl
  map_comp := by intro F G H α β; apply SheafSystem.Hom.ext; intro n; ext V x; rfl

/-- Restriction on sections associated to a commutative-square morphism. -/
private def fromEtaleMap (F : EtaleSystem U) {Y Z : SpacesEtale U} (f : Y ⟶ Z) :=
  (F.map f.simplex).hom.app (op Z.obj) ≫
    (F.obj Y.index.unop).obj.map (SpacesEtale.homEquivToPullback f).op

/-- Assembly on sections respects identities and composition. -/
private abbrev fromEtaleFunctorLaw :=
  ∀ F : EtaleSystem U,
    (∀ Y : SpacesEtale U, fromEtaleMap U F (𝟙 Y) = 𝟙 _) ∧
    (∀ {Y Z W : SpacesEtale U} (f : Y ⟶ Z) (g : Z ⟶ W),
      fromEtaleMap U F (f ≫ g) = fromEtaleMap U F g ≫ fromEtaleMap U F f)

/-- The presheaf assembled by evaluation of the stage sheaves. -/
private def fromEtalePresheaf (h : fromEtaleFunctorLaw U) (F : EtaleSystem U) :
    (SpacesEtale U)ᵒᵖ ⥤ Type (u + 1) where
  obj Y := (F.obj Y.unop.index.unop).obj.obj (op Y.unop.obj)
  map f := fromEtaleMap U F f.unop
  map_id Y := (h F).1 Y.unop
  map_comp f g := (h F).2 g.unop f.unop

/-- Stagewise assembly is a sheaf and carries system maps to natural section maps. -/
private theorem fromEtaleSheafSystem_laws :
    fromEtaleFunctorLaw U ∧
    (∀ (h : fromEtaleFunctorLaw U) (F : EtaleSystem U),
      Presheaf.IsSheaf (spacesEtaleTotalTopology U) (fromEtalePresheaf U h F)) ∧
    (∀ {F G : EtaleSystem U} (α : F ⟶ G)
      {Y Z : SpacesEtale U} (f : Y ⟶ Z),
      fromEtaleMap U F f ≫ (α.app Y.index.unop).hom.app (op Y.obj) =
        (α.app Z.index.unop).hom.app (op Z.obj) ≫ fromEtaleMap U G f) :=
  sorry

/-- Assemble a total étale sheaf from its stage sheaves and transition maps. -/
def fromEtaleSheafSystem :
    EtaleSystem U ⥤ Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)) where
  obj F := ⟨fromEtalePresheaf U (fromEtaleSheafSystem_laws U).1 F,
    (fromEtaleSheafSystem_laws U).2.1 _ F⟩
  map α := ObjectProperty.homMk
    { app := fun Y ↦ (α.app Y.unop.index.unop).hom.app (op Y.unop.obj)
      naturality := fun _ _ f ↦ (fromEtaleSheafSystem_laws U).2.2 α f.unop }
  map_id := by intro F; ext Y x; rfl
  map_comp := by intro F G H α β; ext Y x; rfl

/-- Restriction followed by assembly has identity section maps in both directions. -/
private theorem etaleSheafSystem_unit_naturality
    (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)))
    {Y Z : (SpacesEtale U)ᵒᵖ} (f : Y ⟶ Z) :
    (F.obj.map f ≫ 𝟙 _ = 𝟙 _ ≫
      ((toEtaleSheafSystem U ⋙ fromEtaleSheafSystem U).obj F).obj.map f) ∧
    (((toEtaleSheafSystem U ⋙ fromEtaleSheafSystem U).obj F).obj.map f ≫ 𝟙 _ =
      𝟙 _ ≫ F.obj.map f) :=
  sorry

/-- The identity section comparison from a total sheaf to its restriction and assembly. -/
private def etaleSheafSystemUnit :
    𝟭 (Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))) ≅
      toEtaleSheafSystem U ⋙ fromEtaleSheafSystem U :=
  NatIso.ofComponents (fun F ↦
    { hom := ObjectProperty.homMk
        { app := fun _ ↦ 𝟙 _
          naturality := fun _ _ f ↦ (etaleSheafSystem_unit_naturality U F f).1 }
      inv := ObjectProperty.homMk
        { app := fun _ ↦ 𝟙 _
          naturality := fun _ _ f ↦ (etaleSheafSystem_unit_naturality U F f).2 }
      hom_inv_id := by ext Y x; rfl
      inv_hom_id := by ext Y x; rfl })
    (by intro F G α; ext Y x; rfl)

/-- Assembly followed by restriction has identity section maps on each stage. -/
private theorem etaleSheafSystem_counit_naturality (F : EtaleSystem U) (n : SimplexCategory)
    {V W : (spacesEtaleSite (U.obj (op n)))ᵒᵖ} (f : V ⟶ W) :
    ((((fromEtaleSheafSystem U ⋙ toEtaleSheafSystem U).obj F).obj n).obj.map f ≫ 𝟙 _ =
      𝟙 _ ≫ (F.obj n).obj.map f) ∧
    ((F.obj n).obj.map f ≫ 𝟙 _ =
      𝟙 _ ≫ (((fromEtaleSheafSystem U ⋙ toEtaleSheafSystem U).obj F).obj n).obj.map f) :=
  sorry

/-- The identity stage comparison from restriction of assembly to the original system. -/
private def etaleCounitApp (F : EtaleSystem U) (n : SimplexCategory) :
    ((fromEtaleSheafSystem U ⋙ toEtaleSheafSystem U).obj F).obj n ⟶ F.obj n :=
  ObjectProperty.homMk
    { app := fun _ ↦ 𝟙 _
      naturality := fun _ _ f ↦ (etaleSheafSystem_counit_naturality U F n f).1 }

/-- The inverse identity comparison on stage sections. -/
private def etaleCounitInvApp (F : EtaleSystem U) (n : SimplexCategory) :
    F.obj n ⟶ ((fromEtaleSheafSystem U ⋙ toEtaleSheafSystem U).obj F).obj n :=
  ObjectProperty.homMk
    { app := fun _ ↦ 𝟙 _
      naturality := fun _ _ f ↦ (etaleSheafSystem_counit_naturality U F n f).2 }

/-- The identity stage comparisons commute with all system transitions. -/
private theorem etaleSheafSystem_equivalence_laws (F : EtaleSystem U)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (((fromEtaleSheafSystem U ⋙ toEtaleSheafSystem U).obj F).map φ ≫
      (etaleStageMap U φ).pushforward.map (etaleCounitApp U F n) =
      etaleCounitApp U F m ≫ F.map φ) ∧
    (F.map φ ≫ (etaleStageMap U φ).pushforward.map (etaleCounitInvApp U F n) =
      etaleCounitInvApp U F m ≫
        ((fromEtaleSheafSystem U ⋙ toEtaleSheafSystem U).obj F).map φ) :=
  sorry

/-- The canonical stagewise identity counit of restriction and assembly. -/
private def etaleSheafSystemCounit :
    fromEtaleSheafSystem U ⋙ toEtaleSheafSystem U ≅ 𝟭 (EtaleSystem U) :=
  NatIso.ofComponents (fun F ↦
    { hom := SheafSystem.homMk (etaleCounitApp U F)
        (fun φ ↦ (etaleSheafSystem_equivalence_laws U F φ).1)
      inv := SheafSystem.homMk (etaleCounitInvApp U F)
        (fun φ ↦ (etaleSheafSystem_equivalence_laws U F φ).2)
      hom_inv_id := by apply SheafSystem.Hom.ext; intro n; ext V x; rfl
      inv_hom_id := by apply SheafSystem.Hom.ext; intro n; ext V x; rfl })
    (by intro F G α; apply SheafSystem.Hom.ext; intro n; ext V x; rfl)

/-- Total étale sheaves are equivalent to their systems of stage sheaves. -/
def etaleSheafSystemEquivalence :
    Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)) ≌ EtaleSystem U :=
  CategoryTheory.Equivalence.mk (toEtaleSheafSystem U) (fromEtaleSheafSystem U)
    (etaleSheafSystemUnit U) (etaleSheafSystemCounit U)

variable {X : AlgebraicSpace S} (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- The canonical inverse-image comparison supplied by augmentation naturality. -/
private def etaleAugmentationStageComp {m n : SimplexCategory} (φ : m ⟶ n) :
    (spacesEtaleMorphismOfTopoi (a.app (op m)))⁻¹ ⋙ (etaleStageMap U φ)⁻¹ ≅
      (spacesEtaleMorphismOfTopoi (a.app (op n)))⁻¹ :=
  (spacesEtaleMorphismOfTopoiComp (U.map φ.op) (a.app (op m))).symm ≪≫
    eqToIso (congrArg (fun f ↦ (spacesEtaleMorphismOfTopoi f).inverseImage)
      ((a.naturality φ.op).trans (Category.comp_id _)))

/-- The augmentation inverse-image transition is the mate of the stage comparison. -/
private def etaleAugmentationTransition
    (G : Sheaf (spacesEtaleTopology X) (Type (u + 1)))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (spacesEtaleMorphismOfTopoi (a.app (op m)))⁻¹.obj G ⟶
      (etaleStageMap U φ).pushforward.obj
        ((spacesEtaleMorphismOfTopoi (a.app (op n)))⁻¹.obj G) :=
  (etaleStageMap U φ).adjunction.homEquiv _ _
    ((etaleAugmentationStageComp U a φ).hom.app G)

/-- The augmentation stage inverse images and their canonical transitions are functorial. -/
private theorem spacesEtaleAugmentation_inverseImage_laws :
    (∀ (G : Sheaf (spacesEtaleTopology X) (Type (u + 1))) (n : SimplexCategory),
      etaleAugmentationTransition U a G (𝟙 n) =
        (HasPushforwardFunctoriality.pushforwardIdIso (fHom := fun φ ↦ etaleStageMap U φ) n).inv.app
          ((spacesEtaleMorphismOfTopoi (a.app (op n)))⁻¹.obj G)) ∧
    (∀ (G : Sheaf (spacesEtaleTopology X) (Type (u + 1)))
      {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      etaleAugmentationTransition U a G (ψ ≫ φ) =
        etaleAugmentationTransition U a G ψ ≫ (etaleStageMap U ψ).pushforward.map
          (etaleAugmentationTransition U a G φ) ≫
        (HasPushforwardFunctoriality.pushforwardCompIso (fHom := fun φ ↦ etaleStageMap U φ) ψ φ).hom.app
          ((spacesEtaleMorphismOfTopoi (a.app (op n)))⁻¹.obj G)) ∧
    (∀ {G H : Sheaf (spacesEtaleTopology X) (Type (u + 1))} (α : G ⟶ H)
      {m n : SimplexCategory} (φ : m ⟶ n),
      etaleAugmentationTransition U a G φ ≫ (etaleStageMap U φ).pushforward.map
        ((spacesEtaleMorphismOfTopoi (a.app (op n)))⁻¹.map α) =
      (spacesEtaleMorphismOfTopoi (a.app (op m)))⁻¹.map α ≫ etaleAugmentationTransition U a H φ) :=
  sorry

/-- The system of all stage inverse images along an augmentation. -/
private def etaleAugmentationInverseSystem :
    Sheaf (spacesEtaleTopology X) (Type (u + 1)) ⥤ EtaleSystem U where
  obj G := SheafSystem.of
    (fun n ↦ (spacesEtaleMorphismOfTopoi (a.app (op n)))⁻¹.obj G)
    (fun φ ↦ etaleAugmentationTransition U a G φ)
    ((spacesEtaleAugmentation_inverseImage_laws U a).1 G)
    ((spacesEtaleAugmentation_inverseImage_laws U a).2.1 G)
  map α := SheafSystem.homMk
    (fun n ↦ (spacesEtaleMorphismOfTopoi (a.app (op n)))⁻¹.map α)
    ((spacesEtaleAugmentation_inverseImage_laws U a).2.2 α)
  map_id := by
    intro G; apply SheafSystem.Hom.ext; intro n
    exact (spacesEtaleMorphismOfTopoi (a.app (op n)))⁻¹.map_id G
  map_comp := by
    intro G H K α β; apply SheafSystem.Hom.ext; intro n
    exact (spacesEtaleMorphismOfTopoi (a.app (op n)))⁻¹.map_comp α β

/-- Total inverse image assembled from all stage inverse images. -/
private def etaleAugmentationInverseImage :=
  etaleAugmentationInverseSystem U a ⋙ fromEtaleSheafSystem U

/-- Direct-image comparison corresponding to augmentation naturality. -/
private def etaleAugmentationStagePushforward {m n : SimplexCategory} (φ : m ⟶ n) :
    (etaleStageMap U φ).pushforward ⋙ (spacesEtaleMorphismOfTopoi (a.app (op m))).pushforward ≅
      (spacesEtaleMorphismOfTopoi (a.app (op n))).pushforward :=
  MorphismOfTopoiIn.pushforwardIsoOfInverseImageIso
    ((spacesEtaleMorphismOfTopoi (a.app (op m))).comp (etaleStageMap U φ))
    (spacesEtaleMorphismOfTopoi (a.app (op n))) (etaleAugmentationStageComp U a φ)

/-- The two coface maps between degree-zero and degree-one stage direct images. -/
def spacesEtaleAugmentationParallel
    (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))) (i : Fin 2) :
    (spacesEtaleMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.obj
      (((toEtaleSheafSystem U).obj F).obj ⦋0⦌) ⟶
    (spacesEtaleMorphismOfTopoi (a.app (op ⦋1⦌))).pushforward.obj
      (((toEtaleSheafSystem U).obj F).obj ⦋1⦌) :=
  (spacesEtaleMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.map
    (((toEtaleSheafSystem U).obj F).map (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)) ≫
  (etaleAugmentationStagePushforward U a (SimplexCategory.δ i : ⦋0⦌ ⟶ ⦋1⦌)).hom.app
    (((toEtaleSheafSystem U).obj F).obj ⦋1⦌)

/-- Maps of total sheaves induce maps between the coface equalizers. -/
private theorem spacesEtaleAugmentation_pushforward_laws
    {F G : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))} (α : F ⟶ G) :
    (equalizer.ι (spacesEtaleAugmentationParallel U a F 0) (spacesEtaleAugmentationParallel U a F 1) ≫
      (spacesEtaleMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.map
        (((toEtaleSheafSystem U).map α).app ⦋0⦌)) ≫ spacesEtaleAugmentationParallel U a G 0 =
    (equalizer.ι (spacesEtaleAugmentationParallel U a F 0) (spacesEtaleAugmentationParallel U a F 1) ≫
      (spacesEtaleMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.map
        (((toEtaleSheafSystem U).map α).app ⦋0⦌)) ≫ spacesEtaleAugmentationParallel U a G 1 :=
  sorry

/-- Direct image is the equalizer of the two coface maps on stage direct images. -/
private def etaleAugmentationPushforward :
    Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)) ⥤
      Sheaf (spacesEtaleTopology X) (Type (u + 1)) where
  obj F := equalizer (spacesEtaleAugmentationParallel U a F 0) (spacesEtaleAugmentationParallel U a F 1)
  map α := equalizer.lift
    (equalizer.ι (spacesEtaleAugmentationParallel U a _ 0) (spacesEtaleAugmentationParallel U a _ 1) ≫
      (spacesEtaleMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.map
        (((toEtaleSheafSystem U).map α).app ⦋0⦌))
    (spacesEtaleAugmentation_pushforward_laws U a α)
  map_id := by
    intro F
    apply equalizer.hom_ext
    simp only [equalizer.lift_ι, Functor.map_id]
    change _ ≫ (spacesEtaleMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.map (𝟙 _) = _
    simp
    rfl
  map_comp := by
    intro F G H α β
    apply equalizer.hom_ext
    simp only [Category.assoc, equalizer.lift_ι]
    change _ ≫ (spacesEtaleMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.map
      (((toEtaleSheafSystem U).map (α ≫ β)).app ⦋0⦌) = _
    rw [(toEtaleSheafSystem U).map_comp]
    change _ ≫ (spacesEtaleMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.map
      ((((toEtaleSheafSystem U).map α).app ⦋0⦌) ≫
        (((toEtaleSheafSystem U).map β).app ⦋0⦌)) = _
    rw [Functor.map_comp]
    simp only [← Category.assoc, equalizer.lift_ι]
    congr 1
    exact (equalizer.lift_ι _ _).symm

/-- The degree-zero adjoint of a total sheaf map. -/
private def etaleAugmentationHomToZero
    (G : Sheaf (spacesEtaleTopology X) (Type (u + 1)))
    (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)))
    (α : (etaleAugmentationInverseImage U a).obj G ⟶ F) :=
  (spacesEtaleMorphismOfTopoi (a.app (op ⦋0⦌))).adjunction.homEquiv G
    (((toEtaleSheafSystem U).obj F).obj ⦋0⦌)
    (((etaleSheafSystemCounit U).inv.app ((etaleAugmentationInverseSystem U a).obj G) ≫
      (toEtaleSheafSystem U).map α).app ⦋0⦌)

/-- The degree-zero adjoint coequalizes the two coface maps. -/
private abbrev etaleAugmentationHomToLaw :=
  ∀ (G : Sheaf (spacesEtaleTopology X) (Type (u + 1)))
    (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)))
    (α : (etaleAugmentationInverseImage U a).obj G ⟶ F),
    etaleAugmentationHomToZero U a G F α ≫ spacesEtaleAugmentationParallel U a F 0 =
      etaleAugmentationHomToZero U a G F α ≫ spacesEtaleAugmentationParallel U a F 1

/-- The forward adjunction map factors the degree-zero adjoint through the equalizer. -/
private def etaleAugmentationHomTo (h : etaleAugmentationHomToLaw U a)
    (G : Sheaf (spacesEtaleTopology X) (Type (u + 1)))
    (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)))
    (α : (etaleAugmentationInverseImage U a).obj G ⟶ F) :
    G ⟶ (etaleAugmentationPushforward U a).obj F :=
  equalizer.lift (etaleAugmentationHomToZero U a G F α) (h G F α)

/-- The stage component reconstructed from a map to the equalizer. -/
private def etaleAugmentationHomInvApp
    (G : Sheaf (spacesEtaleTopology X) (Type (u + 1)))
    (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)))
    (β : G ⟶ (etaleAugmentationPushforward U a).obj F) (n : SimplexCategory) :
    (spacesEtaleMorphismOfTopoi (a.app (op n)))⁻¹.obj G ⟶
      ((toEtaleSheafSystem U).obj F).obj n :=
  (etaleAugmentationStageComp U a (SimplexCategory.const ⦋0⦌ n 0)).inv.app G ≫
    (etaleStageMap U (SimplexCategory.const ⦋0⦌ n 0)).inverseImage.map
      (((spacesEtaleMorphismOfTopoi (a.app (op ⦋0⦌))).adjunction.homEquiv G
        (((toEtaleSheafSystem U).obj F).obj ⦋0⦌)).symm
        (β ≫ equalizer.ι (spacesEtaleAugmentationParallel U a F 0) (spacesEtaleAugmentationParallel U a F 1))) ≫
    SheafSystem.mapInverseImage ((toEtaleSheafSystem U).obj F) (SimplexCategory.const ⦋0⦌ n 0)

/-- The reconstructed stage components commute with simplex transitions. -/
private abbrev etaleAugmentationHomInvLaw :=
  ∀ (G : Sheaf (spacesEtaleTopology X) (Type (u + 1)))
    (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)))
    (β : G ⟶ (etaleAugmentationPushforward U a).obj F)
    {m n : SimplexCategory} (φ : m ⟶ n),
    ((etaleAugmentationInverseSystem U a).obj G).map φ ≫
      (etaleStageMap U φ).pushforward.map (etaleAugmentationHomInvApp U a G F β n) =
      etaleAugmentationHomInvApp U a G F β m ≫ ((toEtaleSheafSystem U).obj F).map φ

/-- The inverse adjunction map assembles the reconstructed stage maps. -/
private def etaleAugmentationHomInv (h : etaleAugmentationHomInvLaw U a)
    (G : Sheaf (spacesEtaleTopology X) (Type (u + 1)))
    (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1)))
    (β : G ⟶ (etaleAugmentationPushforward U a).obj F) :
    (etaleAugmentationInverseImage U a).obj G ⟶ F :=
  (fromEtaleSheafSystem U).map
    (SheafSystem.homMk (etaleAugmentationHomInvApp U a G F β) (h G F β)) ≫
    (etaleSheafSystemUnit U).inv.app F

/-- The equalizer adjunction maps are defined and inverse to each other. -/
private theorem spacesEtaleAugmentation_homEquiv_laws :
    etaleAugmentationHomToLaw U a ∧ etaleAugmentationHomInvLaw U a ∧
    ∀ (ht : etaleAugmentationHomToLaw U a) (hi : etaleAugmentationHomInvLaw U a)
      (G : Sheaf (spacesEtaleTopology X) (Type (u + 1)))
      (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))),
    Function.LeftInverse (etaleAugmentationHomInv U a hi G F) (etaleAugmentationHomTo U a ht G F) ∧
    Function.RightInverse (etaleAugmentationHomInv U a hi G F) (etaleAugmentationHomTo U a ht G F) :=
  sorry

/-- The Hom-set equivalence of the total étale augmentation adjunction. -/
private def etaleAugmentationHomEquiv
    (G : Sheaf (spacesEtaleTopology X) (Type (u + 1)))
    (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))) :
    ((etaleAugmentationInverseImage U a).obj G ⟶ F) ≃
      (G ⟶ (etaleAugmentationPushforward U a).obj F) where
  toFun := etaleAugmentationHomTo U a (spacesEtaleAugmentation_homEquiv_laws U a).1 G F
  invFun := etaleAugmentationHomInv U a (spacesEtaleAugmentation_homEquiv_laws U a).2.1 G F
  left_inv := ((spacesEtaleAugmentation_homEquiv_laws U a).2.2 _ _ G F).1
  right_inv := ((spacesEtaleAugmentation_homEquiv_laws U a).2.2 _ _ G F).2

/-- The total augmentation Hom equivalence is natural in both sheaf arguments. -/
private theorem spacesEtaleAugmentation_adjunction_laws :
    (∀ {G' G : Sheaf (spacesEtaleTopology X) (Type (u + 1))}
      {F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))}
      (f : G' ⟶ G) (g : G ⟶ (etaleAugmentationPushforward U a).obj F),
      (etaleAugmentationHomEquiv U a G' F).symm (f ≫ g) =
        (etaleAugmentationInverseImage U a).map f ≫ (etaleAugmentationHomEquiv U a G F).symm g) ∧
    (∀ {G : Sheaf (spacesEtaleTopology X) (Type (u + 1))}
      {F F' : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))}
      (f : (etaleAugmentationInverseImage U a).obj G ⟶ F) (g : F ⟶ F'),
      (etaleAugmentationHomEquiv U a G F') (f ≫ g) =
        (etaleAugmentationHomEquiv U a G F) f ≫ (etaleAugmentationPushforward U a).map g) :=
  sorry

/-- The assembled augmentation inverse image preserves finite limits. -/
private instance spacesEtaleAugmentation_inverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (etaleAugmentationInverseImage U a) :=
  sorry

/-- The total étale augmentation has stagewise inverse image and equalizer direct image. -/
def spacesEtaleAugmentation :
    MorphismOfTopoiIn (spacesEtaleTopology X) (spacesEtaleTotalTopology U) where
  inverseImageFunctor := LeftExactFunctor.of (etaleAugmentationInverseImage U a)
  pushforward := etaleAugmentationPushforward U a
  adjunction := Adjunction.mkOfHomEquiv
    { homEquiv := etaleAugmentationHomEquiv U a
      homEquiv_naturality_left_symm := (spacesEtaleAugmentation_adjunction_laws U a).1
      homEquiv_naturality_right := (spacesEtaleAugmentation_adjunction_laws U a).2 }

/-- Sections of total augmentation inverse image are the corresponding stage inverse-image sections. -/
theorem spacesEtaleAugmentation_inverseImage_obj
    (G : Sheaf (spacesEtaleTopology X) (Type (u + 1))) (Y : SpacesEtale U) :
    ((spacesEtaleAugmentation U a)⁻¹.obj G).obj.obj (op Y) =
      ((spacesEtaleMorphismOfTopoi (a.app Y.index))⁻¹.obj G).obj.obj (op Y.obj) := rfl

/-- Total augmentation direct image is the equalizer of the two coface maps on stage direct images. -/
theorem spacesEtaleAugmentation_pushforward_obj
    (F : Sheaf (spacesEtaleTotalTopology U) (Type (u + 1))) :
    (spacesEtaleAugmentation U a).pushforward.obj F =
      equalizer (spacesEtaleAugmentationParallel U a F 0)
        (spacesEtaleAugmentationParallel U a F 1) := rfl

/-- Restriction of a total étale sheaf to a specified stage. -/
def spacesEtaleRestrict (n : SimplexCategory) :=
  etaleRestriction U (toEtaleSheafSystem_laws U).1 n

/-- Restricting the augmentation inverse image has the same sections as stage inverse image. -/
private theorem spacesEtaleAugmentation_restrict_naturality
    (G : Sheaf (spacesEtaleTopology X) (Type (u + 1))) (n : SimplexCategory)
    {V W : (spacesEtaleSite (U.obj (op n)))ᵒᵖ} (f : V ⟶ W) :
    ((((spacesEtaleAugmentation U a)⁻¹ ⋙ spacesEtaleRestrict U n).obj G).obj.map f ≫ 𝟙 _ =
      𝟙 _ ≫ ((spacesEtaleMorphismOfTopoi (a.app (op n)))⁻¹.obj G).obj.map f) ∧
    (((spacesEtaleMorphismOfTopoi (a.app (op n)))⁻¹.obj G).obj.map f ≫ 𝟙 _ =
      𝟙 _ ≫ (((spacesEtaleAugmentation U a)⁻¹ ⋙ spacesEtaleRestrict U n).obj G).obj.map f) :=
  sorry

/-- In every simplicial degree, total augmentation inverse image restricts to the actual stage inverse image. -/
def spacesEtaleAugmentation_restrict (n : SimplexCategory) :
    (spacesEtaleAugmentation U a)⁻¹ ⋙ spacesEtaleRestrict U n ≅
      (spacesEtaleMorphismOfTopoi (a.app (op n)))⁻¹ :=
  NatIso.ofComponents (fun G ↦
    { hom := ObjectProperty.homMk
        { app := fun _ ↦ 𝟙 _
          naturality := fun _ _ f ↦ (spacesEtaleAugmentation_restrict_naturality U a G n f).1 }
      inv := ObjectProperty.homMk
        { app := fun _ ↦ 𝟙 _
          naturality := fun _ _ f ↦ (spacesEtaleAugmentation_restrict_naturality U a G n f).2 }
      hom_inv_id := by ext V x; rfl
      inv_hom_id := by ext V x; rfl })
    (by intro G H α; ext V x; rfl)

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
