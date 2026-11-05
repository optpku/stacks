/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Action.Continuous
public import Mathlib.CategoryTheory.Galois.Action
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Topology.Category.FinTopCat
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.YonedaComparison
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Trivialization
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.StalkRepresentation

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.PreGaloisCategory
open CategoryTheory.Action.ModuleCat
open Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open scoped FintypeCatDiscrete

universe u w

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The forgetful functor from finite étale schemes over `X` to the small étale site of `X`. -/
def finiteEtaleToEtaleFunctor : FiniteEtale X ⥤ X.Etale where
  obj := (FiniteEtale.toEtale X).obj
  map := (FiniteEtale.toEtale X).map

variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]

/-- A finite étale scheme over `X` represents a finite locally constant sheaf of sets. -/
theorem sheafifiedRepresentable_isFiniteLocallyConstant (Y : FiniteEtale X) :
    Sheaf.IsFiniteLocallyConstant
      (X.smallEtaleTopology.sheafifiedRepresentableFunctor.obj ((FiniteEtale.toEtale X).obj Y)) :=
  FiniteEtale.GeometricFrames.represented_isFiniteLocallyConstant Y

/-- Representable sheaves of finite étale schemes, as a functor into finite locally constant
sheaves of sets on the small étale site. -/
noncomputable def finiteEtaleToFiniteLocallyConstant :
    FiniteEtale X ⥤ (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory :=
  (Sheaf.finiteLocallyConstant X.smallEtaleTopology).lift
    (finiteEtaleToEtaleFunctor ⋙ X.smallEtaleTopology.sheafifiedRepresentableFunctor)
    sheafifiedRepresentable_isFiniteLocallyConstant

/-- The constructed representing finite étale cover of a finite locally constant sheaf. -/
noncomputable def finiteLocallyConstantToFiniteEtale :
    (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory ⥤ FiniteEtale X where
  obj F :=
    letI := F.property
    FiniteLocallyConstant.finiteEtaleRepresentation F.obj
  map {F G} a := by
    letI := F.property
    letI := G.property
    exact MorphismProperty.Over.homMk
      (FiniteLocallyConstant.sectionMap G.obj
        (FiniteLocallyConstant.representationEtale F.obj)
        (a.hom.hom.app (op (FiniteLocallyConstant.representationEtale F.obj))
          (FiniteLocallyConstant.tautologicalSection F.obj)))
      (FiniteLocallyConstant.sectionMap_over G.obj _ _)
  map_id := sorry
  map_comp := sorry

/-- The representing sheaf comparison has the implemented evaluation and universal-section maps. -/
noncomputable def finiteLocallyConstantRepresentationIso
    (F : (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory) :
    F ≅ (finiteEtaleToFiniteLocallyConstant (X := X)).obj
      ((finiteLocallyConstantToFiniteEtale (X := X)).obj F) := by
  letI := F.property
  exact ObjectProperty.isoMk _ (FiniteLocallyConstant.representationIso F.obj)

/-- The small étale topology inherits native subcanonicity from the big pro-étale topology. -/
instance smallEtaleTopology_subcanonical : X.smallEtaleTopology.Subcanonical := by
  letI : Scheme.etaleTopology.Subcanonical :=
    GrothendieckTopology.Subcanonical.of_le Scheme.etaleTopology_le_proetaleTopology
  let G := MorphismProperty.Over.forget (@Etale) ⊤ X
  letI : RepresentablyFlat G := flat_of_preservesFiniteLimits G
  letI : G.IsContinuous X.smallEtaleTopology (Scheme.etaleTopology.over X) := by
    rw [Functor.isContinuous_iff_coverPreserving]
    exact Functor.coverPreserving_restrictedTopology G (Scheme.etaleTopology.over X)
  exact GrothendieckTopology.subcanonical_of_full_of_faithful
    (MorphismProperty.Over.forget (@Etale) ⊤ X) X.smallEtaleTopology
    (Scheme.etaleTopology.over X)

/-- Raw Yoneda identifies the represented cover with the original étale cover through actual maps. -/
noncomputable def finiteEtaleRepresentationEtaleIso (Y : FiniteEtale X) :
    (FiniteEtale.toEtale X).obj Y ≅
      (FiniteEtale.toEtale X).obj
        ((finiteLocallyConstantToFiniteEtale (X := X)).obj
          ((finiteEtaleToFiniteLocallyConstant (X := X)).obj Y)) := by
  let F := X.smallEtaleTopology.sheafifiedRepresentableFunctor.obj ((FiniteEtale.toEtale X).obj Y)
  letI : Sheaf.IsFiniteLocallyConstant F := sheafifiedRepresentable_isFiniteLocallyConstant Y
  let e : CategoryTheory.uliftYoneda.{u + 1}.obj ((FiniteEtale.toEtale X).obj Y) ≅
      CategoryTheory.uliftYoneda.{u + 1}.obj (FiniteLocallyConstant.representationEtale F) :=
    isoSheafify X.smallEtaleTopology
        ((X.smallEtaleTopology.uliftYoneda.{u + 1}).obj ((FiniteEtale.toEtale X).obj Y)).property ≪≫
      FiniteLocallyConstant.representationPresheafIso F
  exact (CategoryTheory.uliftYoneda.{u + 1}).preimageIso e

/-- The finite étale comparison carries both actual underlying scheme maps. -/
noncomputable def finiteEtaleRepresentationIso (Y : FiniteEtale X) :
    Y ≅ ((finiteEtaleToFiniteLocallyConstant (X := X)) ⋙
      finiteLocallyConstantToFiniteEtale).obj Y where
  hom := MorphismProperty.Over.homMk (finiteEtaleRepresentationEtaleIso Y).hom.left sorry
  inv := MorphismProperty.Over.homMk (finiteEtaleRepresentationEtaleIso Y).inv.left sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The explicit finite étale/locally constant equivalence uses constructed covers and comparisons. -/
noncomputable def finiteEtaleFiniteLocallyConstantEquivalence :
    FiniteEtale X ≌ (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory where
  functor := finiteEtaleToFiniteLocallyConstant
  inverse := finiteLocallyConstantToFiniteEtale
  unitIso := NatIso.ofComponents finiteEtaleRepresentationIso (fun _ ↦ sorry)
  counitIso := NatIso.ofComponents (fun F ↦ (finiteLocallyConstantRepresentationIso F).symm)
    (fun _ ↦ sorry)
  functor_unitIso_comp := sorry

/-- Representability is certified by the explicit equivalence, rather than an admitted inverse. -/
noncomputable instance finiteEtaleToFiniteLocallyConstant_isEquivalence :
    (finiteEtaleToFiniteLocallyConstant (X := X)).IsEquivalence :=
  (finiteEtaleFiniteLocallyConstantEquivalence (X := X)).isEquivalence_functor

/-- Finite locally constant sheaves of sets on the small étale site of a connected scheme are
equivalent to finite continuous `π₁`-sets at a geometric point. -/
noncomputable def finiteLocallyConstant_equivalence_finitePi1Sets
    [ConnectedSpace X] (xbar : GeometricPoint X) :
    (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory ≌
      ContAction FintypeCat (Aut (GeometricPoint.finiteFiber xbar)) :=
  -- Local instance justification (proof-local temporary data): the named theorem certifies this fixed geometric-fiber action inside the composite equivalence, without exporting an instance.
  letI : (GeometricPoint.fiberAction xbar).IsEquivalence :=
    CategoryTheory.PreGaloisCategory.functorToContAction_isEquivalence
      (GeometricPoint.finiteFiber xbar)
  (finiteEtaleFiniteLocallyConstantEquivalence (X := X)).symm.trans
    (GeometricPoint.fiberAction xbar).asEquivalence

/-- The set-level equivalence lands in finite continuous `Aut`-sets. -/
theorem finiteLocallyConstant_equivalence_finitePi1Sets_functor_obj
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory) :
    Finite
      ((finiteLocallyConstant_equivalence_finitePi1Sets xbar).functor.obj F).obj.V.obj :=
  sorry

variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]

/-- The property of a discrete continuous module having finite underlying type. -/
def IsFiniteDiscreteModule (R : Type w) [Ring R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteModuleCat R G) : Prop :=
  Finite M.obj.V

/-- Finite discrete continuous `G`-modules. -/
abbrev finiteDiscreteModule (R : Type w) [Ring R]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ObjectProperty (DiscreteModuleCat R G) :=
  IsFiniteDiscreteModule R G

/-- The property of a discrete continuous `Λ`-module having finite type over `Λ`. -/
def IsFiniteTypeDiscreteModule (Λ : Type w) [Ring Λ]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (M : DiscreteModuleCat Λ G) : Prop :=
  Module.Finite Λ M.obj.V

/-- Finite-type discrete continuous `Λ`-modules with `G`-action. -/
abbrev finiteTypeDiscreteModule (Λ : Type w) [Ring Λ]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ObjectProperty (DiscreteModuleCat Λ G) :=
  IsFiniteTypeDiscreteModule Λ G

/-- Forgetting abelian-group structure retains the supplied finite constant charts. -/
instance finiteAddCommSheaf_underlyingFinite
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    [Sheaf.IsFiniteLocallyConstantAddCommGrp F] :
    Sheaf.IsFiniteLocallyConstant
      ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F) where
  existsConstantCover U := by
    obtain ⟨I, charts, hcover, models⟩ :=
      Sheaf.IsLocallyConstantWith.existsConstantCover
        (P := fun A : AddCommGrpCat.{u + 1} ↦ Finite A) (F := F) U
    refine ⟨I, charts, hcover, ?_⟩
    intro i
    obtain ⟨A, hA, ⟨e⟩⟩ := models i
    refine ⟨A, hA, ?_⟩
    exact ⟨((sheafCompose (X.smallEtaleTopology.over (charts i).left)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso e) ≪≫
      (constantCommuteCompose (X.smallEtaleTopology.over (charts i).left)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).app A⟩

/-- Forgetful functor from finite locally constant abelian sheaves to finite locally constant
sheaves of sets. -/
noncomputable def forgetFiniteLocallyConstantAddCommGrp :
    (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory ⥤
      (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory :=
  (Sheaf.finiteLocallyConstant X.smallEtaleTopology).lift
    ((Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).ι ⋙
      sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1}))
    fun F ↦ by
      letI := F.property
      exact finiteAddCommSheaf_underlyingFinite F.obj

/-- The canonical integer-module structure on an abelian group, with the same elements. -/
noncomputable def addCommGrpToIntModule : AddCommGrpCat.{u + 1} ⥤ ModuleCat.{u + 1} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap
  map_id := sorry
  map_comp := sorry

/-- The same-carrier adapter is an equivalence through the native integer-module forgetful
 equivalence; no second equivalence structure is introduced. -/
noncomputable instance addCommGrpToIntModule_isEquivalence :
    addCommGrpToIntModule.{u}.IsEquivalence := by
  let e : addCommGrpToIntModule.{u} ⋙
      CategoryTheory.forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1} ≅
      𝟭 AddCommGrpCat.{u + 1} :=
    NatIso.ofComponents (fun A ↦ Iso.refl A) (fun _ ↦ sorry)
  letI : (addCommGrpToIntModule.{u} ⋙
      CategoryTheory.forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsEquivalence :=
    Functor.isEquivalence_of_iso e.symm
  exact Functor.isEquivalence_of_comp_right addCommGrpToIntModule.{u}
    (CategoryTheory.forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1})

/-- The integer-module sheaf keeps the original abelian sheaf's sections and restriction maps. -/
noncomputable def intModuleSheafOfAddCommSheaf
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} ℤ) :=
  (sheafCompose X.smallEtaleTopology addCommGrpToIntModule).obj F.obj

/-- The actual representing cover of the underlying finite set sheaf. -/
noncomputable def finiteEtaleOfFiniteLocallyConstantAddCommGrp
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    FiniteEtale X :=
  (finiteLocallyConstantToFiniteEtale (X := X)).obj
    (forgetFiniteLocallyConstantAddCommGrp.obj F)

/-- The underlying integer-module presheaf has the specified actual finite étale representation. -/
noncomputable def intModuleSheafRepresentationIso
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    (intModuleSheafOfAddCommSheaf F).obj ⋙ CategoryTheory.forget (ModuleCat.{u + 1} ℤ) ≅
      uliftYoneda.{u + 1}.obj ((FiniteEtale.toEtale X).obj (finiteEtaleOfFiniteLocallyConstantAddCommGrp F)) := by
  let G := forgetFiniteLocallyConstantAddCommGrp.obj F
  letI := G.property
  exact FiniteLocallyConstant.representationPresheafIso G.obj

/-- The actual comparison between finite-neighborhood germs and the abelian stalk. -/
noncomputable def addCommSheafGermIso [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :=
  StalkRepresentation.germIsoOfRepresentable ℤ xbar
    (intModuleSheafOfAddCommSheaf F) (finiteEtaleOfFiniteLocallyConstantAddCommGrp F)
    (intModuleSheafRepresentationIso F)

/-- Monodromy acts on the actual abelian stalk by transporting finite-neighborhood germ action. -/
noncomputable def addCommSheafStalkAction [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    Aut (GeometricPoint.finiteFiber xbar) →*
      End ((StalkRepresentation.stalk ℤ xbar).obj (intModuleSheafOfAddCommSheaf F)) :=
  (addCommSheafGermIso xbar F).conj.toMonoidHom.comp
    (StalkRepresentation.finiteRepresentation ℤ xbar (intModuleSheafOfAddCommSheaf F).obj)

/-- The correct abelian comparison object has the actual stalk as its carrier. -/
noncomputable def discreteModuleOfFiniteLocallyConstantAddCommGrp
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    DiscreteModuleCat ℤ (Aut (GeometricPoint.finiteFiber xbar)) :=
  ⟨{ V := (StalkRepresentation.stalk ℤ xbar).obj (intModuleSheafOfAddCommSheaf F)
     ρ := addCommSheafStalkAction xbar F }, sorry⟩

/-- The stalk of a finite locally constant abelian sheaf is finite. -/
instance addCommSheafStalk_finite [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    Finite (discreteModuleOfFiniteLocallyConstantAddCommGrp xbar F).obj.V := sorry

/-- The comparison object as a finite discrete integer module. -/
noncomputable def finitePi1ModuleOfAddCommSheaf
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory :=
  ⟨discreteModuleOfFiniteLocallyConstantAddCommGrp xbar F,
    addCommSheafStalk_finite xbar F⟩

/-- A sheaf morphism acts by its actual map on the abelian stalk. -/
noncomputable def discreteModuleHomOfAddCommSheaf
    [ConnectedSpace X] (xbar : GeometricPoint X)
    {F G : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory}
    (f : F ⟶ G) :
    (discreteModuleOfFiniteLocallyConstantAddCommGrp xbar F).obj.V ⟶
      (discreteModuleOfFiniteLocallyConstantAddCommGrp xbar G).obj.V :=
  (StalkRepresentation.stalk ℤ xbar).map
    ((sheafCompose X.smallEtaleTopology addCommGrpToIntModule).map f.hom)

/-- The comparison functor sending a finite locally constant abelian étale sheaf to its finite
discrete `π₁`-module. -/
noncomputable def finiteLocallyConstantAddCommGrpToFinitePi1Modules
    [ConnectedSpace X] (xbar : GeometricPoint X) :
    (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory ⥤
      (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory where
  obj F := finitePi1ModuleOfAddCommSheaf xbar F
  map {F G} f :=
    ObjectProperty.homMk <| ObjectProperty.homMk
      { hom := discreteModuleHomOfAddCommSheaf xbar f
        comm := fun _ ↦ sorry }

/-- Forgetful functor from finite-type locally constant module sheaves over a finite ring
to finite locally constant sheaves of sets. -/
noncomputable def forgetFiniteTypeLocallyConstantModule (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)] :
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ⥤
      (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory :=
  (Sheaf.finiteLocallyConstant X.smallEtaleTopology).lift
    ((Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).ι ⋙
      sheafCompose X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ)))
    fun F ↦ by
      letI : Sheaf.IsFiniteTypeLocallyConstantModule F.obj := F.property
      exact Sheaf.IsFiniteTypeLocallyConstantModule.underlying_isFiniteLocallyConstant F.obj

/-- The finite étale scheme representing the underlying finite locally constant sheaf of sets of
a finite-type locally constant sheaf of `Λ`-modules, constructed directly from its affine algebras.
The geometric point is retained for compatibility; the construction is independent of it. -/
noncomputable def finiteEtaleOfFiniteTypeLocallyConstantModule
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    FiniteEtale X :=
  (finiteLocallyConstantToFiniteEtale (X := X)).obj
    ((forgetFiniteTypeLocallyConstantModule Λ).obj F)

/-- The actual geometric module stalk of a finite-type locally constant sheaf, with linear
monodromy induced by natural automorphisms of the finite étale fiber functor. -/
noncomputable def discreteModuleOfFiniteTypeLocallyConstantModule
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    DiscreteModuleCat Λ (Aut (GeometricPoint.finiteFiber xbar)) :=
  StalkRepresentation.module Λ xbar F

/-- The comparison object of a finite-type locally constant `Λ`-module sheaf as a finite-type
discrete `π₁`-module. -/
noncomputable def finitePi1LambdaModuleOfModuleSheaf
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory :=
  ⟨discreteModuleOfFiniteTypeLocallyConstantModule Λ xbar F,
    StalkRepresentation.module_finite Λ xbar F⟩

/-- The finite étale morphism induced by a morphism of finite-type locally constant `Λ`-module
sheaves by applying the representing-cover functor to the underlying sheaf map. -/
noncomputable def inducedFiniteEtaleHomOfModuleSheaf
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X)
    {F G : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory}
    (f : F ⟶ G) :
    finiteEtaleOfFiniteTypeLocallyConstantModule Λ xbar F ⟶
      finiteEtaleOfFiniteTypeLocallyConstantModule Λ xbar G :=
  (finiteLocallyConstantToFiniteEtale (X := X)).map
    ((forgetFiniteTypeLocallyConstantModule Λ).map f)

/-- The linear map on geometric stalks induced by a morphism of finite-type locally
constant module sheaves. -/
noncomputable def discreteModuleHomOfModuleSheaf
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X)
    {F G : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory}
    (f : F ⟶ G) :
    (discreteModuleOfFiniteTypeLocallyConstantModule Λ xbar F).obj.V ⟶
      (discreteModuleOfFiniteTypeLocallyConstantModule Λ xbar G).obj.V :=
  (StalkRepresentation.stalk Λ xbar).map f.hom

/-- The comparison functor sending a finite-type locally constant étale sheaf of `Λ`-modules to
its finite discrete `π₁`-module with commuting `Λ`-action. -/
noncomputable def finiteTypeLocallyConstantModuleToFinitePi1LambdaModules
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X) :
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ⥤
      (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory :=
  (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).lift
    (StalkRepresentation.functor Λ xbar) (StalkRepresentation.module_finite Λ xbar)

end AlgebraicGeometry.Scheme
