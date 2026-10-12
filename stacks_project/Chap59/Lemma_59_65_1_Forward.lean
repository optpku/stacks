/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
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
public import stacks_project.Chap58.Theorem_58_6_2
public import stacks_project.Chap59.Lemma_59_64_4
public import stacks_project.Chap59.Lemma_59_65_1_StalkRepresentation

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
  obj := finiteEtaleToEtale
  map := finiteEtaleToEtaleMap

variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]

/-- A finite étale scheme over `X` represents a finite locally constant sheaf of sets. -/
theorem sheafifiedRepresentable_isFiniteLocallyConstant (Y : FiniteEtale X) :
    Sheaf.IsFiniteLocallyConstant
      (X.smallEtaleTopology.sheafifiedRepresentableFunctor.obj (finiteEtaleToEtale Y)) := sorry

/-- Representable sheaves of finite étale schemes, as a functor into finite locally constant
sheaves of sets on the small étale site. -/
noncomputable def finiteEtaleToFiniteLocallyConstant :
    FiniteEtale X ⥤ (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory :=
  (Sheaf.finiteLocallyConstant X.smallEtaleTopology).lift
    (finiteEtaleToEtaleFunctor ⋙ X.smallEtaleTopology.sheafifiedRepresentableFunctor)
    sheafifiedRepresentable_isFiniteLocallyConstant

/-- Representability of finite locally constant étale sheaves of sets by finite étale schemes is
an equivalence. -/
noncomputable instance finiteEtaleToFiniteLocallyConstant_isEquivalence :
    (finiteEtaleToFiniteLocallyConstant (X := X)).IsEquivalence := sorry

/-- Finite locally constant sheaves of sets on the small étale site of a connected scheme are
equivalent to finite continuous `π₁`-sets at a geometric point. -/
noncomputable def finiteLocallyConstant_equivalence_finitePi1Sets
    [ConnectedSpace X] (xbar : GeometricPoint X) :
    (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory ≌
      ContAction FintypeCat (Aut (standardFiniteEtaleFiber xbar)) :=
  -- Local instance justification (proof-local temporary data): the named theorem certifies this fixed geometric-fiber action inside the composite equivalence, without exporting an instance.
  letI : (functorToContAction_finiteEtaleFiber xbar).IsEquivalence :=
    finiteEtaleFiber_functorToContAction_isEquivalence xbar
  (finiteEtaleToFiniteLocallyConstant (X := X)).asEquivalence.symm.trans
    (functorToContAction_finiteEtaleFiber xbar).asEquivalence

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

/-- Forgetful functor from finite locally constant abelian sheaves to finite locally constant
sheaves of sets. -/
noncomputable def forgetFiniteLocallyConstantAddCommGrp :
    (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory ⥤
      (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory :=
  (Sheaf.finiteLocallyConstant X.smallEtaleTopology).lift
    ((Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).ι ⋙
      sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1}))
    fun _ ↦ sorry

/-- The finite étale scheme representing the underlying finite locally constant sheaf of sets of
a finite locally constant abelian sheaf, via the set-level Galois equivalence. -/
noncomputable def finiteEtaleOfFiniteLocallyConstantAddCommGrp
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    FiniteEtale X :=
  -- Local instance justification (proof-local temporary data): supply the named proof to this fixed fiber-action inverse object; the representing functor and ambient instance table remain unchanged.
  letI : (functorToContAction_finiteEtaleFiber xbar).IsEquivalence :=
    finiteEtaleFiber_functorToContAction_isEquivalence xbar
  (functorToContAction_finiteEtaleFiber xbar).asEquivalence.inverse.obj
    ((finiteLocallyConstant_equivalence_finitePi1Sets xbar).functor.obj
      (forgetFiniteLocallyConstantAddCommGrp.obj F))

/-- The automorphism of the representing finite étale scheme induced by a fundamental-group
element acting on the underlying `π₁`-set. -/
noncomputable def autHomOnFiniteEtaleOfAddCommSheaf
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory)
    (σ : Aut (standardFiniteEtaleFiber xbar)) :
    finiteEtaleOfFiniteLocallyConstantAddCommGrp xbar F ⟶
      finiteEtaleOfFiniteLocallyConstantAddCommGrp xbar F :=
  -- Local instance justification (proof-local temporary data): this named proof is consumed only by the fixed inverse.map carrying the specified automorphism, without selecting another action functor.
  letI : (functorToContAction_finiteEtaleFiber xbar).IsEquivalence :=
    finiteEtaleFiber_functorToContAction_isEquivalence xbar
  let S := (finiteLocallyConstant_equivalence_finitePi1Sets xbar).functor.obj
      (forgetFiniteLocallyConstantAddCommGrp.obj F)
  (functorToContAction_finiteEtaleFiber xbar).asEquivalence.inverse.map
    (ObjectProperty.homMk { hom := S.obj.ρ σ, comm := fun _ ↦ sorry })

/-- The discrete `π₁`-module of sections of a finite locally constant abelian sheaf on its
representing finite étale scheme, with transported `Aut`-action. -/
noncomputable def discreteModuleOfFiniteLocallyConstantAddCommGrp
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    DiscreteModuleCat ℤ (Aut (standardFiniteEtaleFiber xbar)) :=
  let A := F.obj.obj.obj
      (op (finiteEtaleToEtale (finiteEtaleOfFiniteLocallyConstantAddCommGrp xbar F)))
  let V := ModuleCat.of ℤ A
  let rho : Aut (standardFiniteEtaleFiber xbar) →* End V :=
    { toFun := fun σ ↦
        ModuleCat.ofHom
          (F.obj.obj.map
              (op (finiteEtaleToEtaleMap
                (autHomOnFiniteEtaleOfAddCommSheaf xbar F σ)))).hom.toIntLinearMap
      map_one' := sorry
      map_mul' := sorry }
  ⟨{ V := V, ρ := rho }, fun _ ↦ sorry⟩

/-- The comparison object of a finite locally constant abelian sheaf as a finite discrete
`π₁`-module. -/
noncomputable def finitePi1ModuleOfAddCommSheaf
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    (finiteDiscreteModule ℤ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory :=
  ⟨discreteModuleOfFiniteLocallyConstantAddCommGrp xbar F, sorry⟩

/-- The finite étale morphism induced by a morphism of finite locally constant abelian sheaves
via the set-level Galois equivalence on underlying sheaves of sets. -/
noncomputable def inducedFiniteEtaleHomOfAddCommSheaf
    [ConnectedSpace X] (xbar : GeometricPoint X)
    {F G : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory}
    (f : F ⟶ G) :
    finiteEtaleOfFiniteLocallyConstantAddCommGrp xbar F ⟶
      finiteEtaleOfFiniteLocallyConstantAddCommGrp xbar G :=
  -- Local instance justification (proof-local temporary data): certify the same fixed inverse.map used for both representing objects; this local proof changes neither the sheaf morphism nor exported instances.
  letI : (functorToContAction_finiteEtaleFiber xbar).IsEquivalence :=
    finiteEtaleFiber_functorToContAction_isEquivalence xbar
  (functorToContAction_finiteEtaleFiber xbar).asEquivalence.inverse.map
    ((finiteLocallyConstant_equivalence_finitePi1Sets xbar).functor.map
      (forgetFiniteLocallyConstantAddCommGrp.map f))

/-- The `ℤ`-linear map on discrete `π₁`-modules induced by a morphism of finite locally constant
abelian sheaves, as the component of `f` on the representing finite étale object of the source,
transported along the induced finite étale morphism. -/
noncomputable def discreteModuleHomOfAddCommSheaf
    [ConnectedSpace X] (xbar : GeometricPoint X)
    {F G : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory}
    (f : F ⟶ G) :
    (discreteModuleOfFiniteLocallyConstantAddCommGrp xbar F).obj.V ⟶
      (discreteModuleOfFiniteLocallyConstantAddCommGrp xbar G).obj.V :=
  let YF := finiteEtaleOfFiniteLocallyConstantAddCommGrp xbar F
  let appF := f.hom.hom.app (op (finiteEtaleToEtale YF))
  let res := G.obj.obj.map
      (op (finiteEtaleToEtaleMap (inducedFiniteEtaleHomOfAddCommSheaf xbar f)))
  ModuleCat.ofHom
    { toFun := fun a ↦ Function.invFun res.hom (appF.hom a)
      map_add' := sorry
      map_smul' := sorry }

/-- The comparison functor sending a finite locally constant abelian étale sheaf to its finite
discrete `π₁`-module. -/
noncomputable def finiteLocallyConstantAddCommGrpToFinitePi1Modules
    [ConnectedSpace X] (xbar : GeometricPoint X) :
    (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory ⥤
      (finiteDiscreteModule ℤ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory where
  obj F := finitePi1ModuleOfAddCommSheaf xbar F
  map {F G} f :=
    ObjectProperty.homMk <| ObjectProperty.homMk
      { hom := discreteModuleHomOfAddCommSheaf xbar f
        comm := fun _ ↦ sorry }

/-- The abelian comparison functor is an equivalence. -/
noncomputable instance finiteLocallyConstantAddCommGrpToFinitePi1Modules_isEquivalence
    [ConnectedSpace X] (xbar : GeometricPoint X) :
    (finiteLocallyConstantAddCommGrpToFinitePi1Modules xbar).IsEquivalence := sorry

/-- Finite locally constant abelian étale sheaves are equivalent to finite discrete
`π₁`-modules. -/
noncomputable def finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules
    [ConnectedSpace X] (xbar : GeometricPoint X) :
    (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory ≌
      (finiteDiscreteModule ℤ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory :=
  (finiteLocallyConstantAddCommGrpToFinitePi1Modules xbar).asEquivalence

/-- The abelian equivalence sends a finite locally constant sheaf to a finite discrete
`π₁`-module. -/
theorem finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules_functor_obj
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    IsFiniteDiscreteModule ℤ (Aut (standardFiniteEtaleFiber xbar))
      ((finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules xbar).functor.obj F).obj :=
  sorry

/-- Forgetful functor from finite-type locally constant module sheaves to finite locally
constant sheaves of sets. -/
noncomputable def forgetFiniteTypeLocallyConstantModule (Λ : Type (u + 1)) [Ring Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)] :
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ⥤
      (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory :=
  (Sheaf.finiteLocallyConstant X.smallEtaleTopology).lift
    ((Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).ι ⋙
      sheafCompose X.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} Λ)))
    fun _ ↦ sorry

/-- The finite étale scheme representing the underlying finite locally constant sheaf of sets of
a finite-type locally constant sheaf of `Λ`-modules. -/
noncomputable def finiteEtaleOfFiniteTypeLocallyConstantModule
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    FiniteEtale X :=
  -- Local instance justification (proof-local temporary data): reuse the named equivalence proof for this finite-module underlying-set inverse object, keeping the chosen geometric-fiber functor fixed.
  letI : (functorToContAction_finiteEtaleFiber xbar).IsEquivalence :=
    finiteEtaleFiber_functorToContAction_isEquivalence xbar
  (functorToContAction_finiteEtaleFiber xbar).asEquivalence.inverse.obj
    ((finiteLocallyConstant_equivalence_finitePi1Sets xbar).functor.obj
      ((forgetFiniteTypeLocallyConstantModule Λ).obj F))

/-- The actual geometric module stalk of a finite-type locally constant sheaf, with linear
monodromy induced by natural automorphisms of the finite étale fiber functor. -/
noncomputable def discreteModuleOfFiniteTypeLocallyConstantModule
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar)) :=
  StalkRepresentation.module Λ xbar F

/-- The comparison object of a finite-type locally constant `Λ`-module sheaf as a finite-type
discrete `π₁`-module. -/
noncomputable def finitePi1LambdaModuleOfModuleSheaf
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory :=
  ⟨discreteModuleOfFiniteTypeLocallyConstantModule Λ xbar F,
    StalkRepresentation.module_finite Λ xbar F⟩

/-- The finite étale morphism induced by a morphism of finite-type locally constant `Λ`-module
sheaves via the set-level Galois equivalence on underlying sheaves of sets. -/
noncomputable def inducedFiniteEtaleHomOfModuleSheaf
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X)
    {F G : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory}
    (f : F ⟶ G) :
    finiteEtaleOfFiniteTypeLocallyConstantModule Λ xbar F ⟶
      finiteEtaleOfFiniteTypeLocallyConstantModule Λ xbar G :=
  -- Local instance justification (proof-local temporary data): the named proof supplies only this fixed inverse.map on the given module-sheaf morphism; no new equivalence or global instance is introduced.
  letI : (functorToContAction_finiteEtaleFiber xbar).IsEquivalence :=
    finiteEtaleFiber_functorToContAction_isEquivalence xbar
  (functorToContAction_finiteEtaleFiber xbar).asEquivalence.inverse.map
    ((finiteLocallyConstant_equivalence_finitePi1Sets xbar).functor.map
      ((forgetFiniteTypeLocallyConstantModule Λ).map f))

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
      (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory :=
  (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).lift
    (StalkRepresentation.functor Λ xbar) (StalkRepresentation.module_finite Λ xbar)

end AlgebraicGeometry.Scheme
