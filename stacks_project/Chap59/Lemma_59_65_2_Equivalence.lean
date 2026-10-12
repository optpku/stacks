/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Lemma_59_65_1_Equivalence
public import stacks_project.Chap59.Lemma_59_75_6_Stalk

@[expose] public section

open CategoryTheory
open CategoryTheory.CategoryOfElements
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Action.ModuleCat
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- Geometric stalk of an étale sheaf of `Λ`-modules, at universe `u+1` matching
`ModuleCat` on the small étale site of `Scheme.{u}`. -/
noncomputable def étaleModuleStalk₁ (Λ : Type (u + 1)) [Ring Λ] (xbar : GeometricPoint X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ModuleCat.{u + 1} Λ :=
  (toSmallEtalePoint xbar).presheafFiber.obj F.obj

/-- The linear map of geometric stalks induced by a morphism of étale sheaves of
`Λ`-modules. -/
noncomputable def étaleModuleStalk₁Map (Λ : Type (u + 1)) [Ring Λ] (xbar : GeometricPoint X)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (f : F ⟶ G) :
    étaleModuleStalk₁ Λ xbar F ⟶ étaleModuleStalk₁ Λ xbar G :=
  (toSmallEtalePoint xbar).presheafFiber.map f.hom

/-- The Type-valued standard finite étale fiber functor at a geometric point. -/
noncomputable abbrev standardFiniteEtaleFiberType [ConnectedSpace X] (xbar : GeometricPoint X) :
    FiniteEtale X ⥤ Type u :=
  standardFiniteEtaleFiber xbar ⋙ FintypeCat.incl

/-- The diagram of values of an étale module sheaf on finite étale neighborhoods of
the geometric point. -/
noncomputable def finiteEtaleNeighborhoodModuleDiagram (Λ : Type (u + 1)) [Ring Λ]
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (standardFiniteEtaleFiberType xbar).Elementsᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
  (π (standardFiniteEtaleFiberType xbar)).op ⋙ finiteEtaleToEtaleFunctor.op ⋙ F.obj

/-- The functor on finite étale neighborhoods induced by an automorphism of the
standard finite étale fiber functor. -/
noncomputable def pi1MapOnFiniteEtaleNeighborhoods [ConnectedSpace X] (xbar : GeometricPoint X)
    (σ : Aut (standardFiniteEtaleFiber xbar)) :
    (standardFiniteEtaleFiberType xbar).Elements ⥤
      (standardFiniteEtaleFiberType xbar).Elements :=
  CategoryOfElements.map (Functor.whiskerRight σ.hom FintypeCat.incl)

/-- For a finite-type locally constant étale sheaf of modules, the geometric stalk
coincides with the colimit over finite étale neighborhoods. -/
theorem étaleModuleStalk₁_eq_colimit_finiteEtaleNeighborhoods (Λ : Type (u + 1)) [Ring Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [IrreducibleSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    étaleModuleStalk₁ Λ xbar F.obj =
      colimit (finiteEtaleNeighborhoodModuleDiagram Λ xbar F.obj) := sorry

/-- Reindexing the finite étale neighborhood diagram by a fiber automorphism does
not change the colimit of a finite-type locally constant module sheaf. -/
theorem colimit_pi1MapOnFiniteEtaleNeighborhoods_eq_étaleModuleStalk₁
    (Λ : Type (u + 1)) [Ring Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [IrreducibleSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory)
    (σ : Aut (standardFiniteEtaleFiber xbar)) :
    colimit ((pi1MapOnFiniteEtaleNeighborhoods xbar σ).op ⋙
        finiteEtaleNeighborhoodModuleDiagram Λ xbar F.obj) =
      étaleModuleStalk₁ Λ xbar F.obj := sorry

/-- The `π₁`-action on the geometric stalk of a finite-type locally constant étale
sheaf of `Λ`-modules, as a monoid homomorphism from `Aut` of the standard finite
étale fiber functor. -/
noncomputable def pi1HomOnEtaleModuleStalk (Λ : Type (u + 1)) [Ring Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [IrreducibleSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    Aut (standardFiniteEtaleFiber xbar) →* End (étaleModuleStalk₁ Λ xbar F.obj) where
  toFun σ :=
    eqToHom (colimit_pi1MapOnFiniteEtaleNeighborhoods_eq_étaleModuleStalk₁ Λ xbar F σ).symm ≫
      colimit.pre (finiteEtaleNeighborhoodModuleDiagram Λ xbar F.obj)
        (pi1MapOnFiniteEtaleNeighborhoods xbar σ).op ≫
      eqToHom (étaleModuleStalk₁_eq_colimit_finiteEtaleNeighborhoods Λ xbar F).symm
  map_one' := sorry
  map_mul' := sorry

/-- The discrete continuous `π₁`-module associated to a finite-type locally constant
étale sheaf of `Λ`-modules, with underlying module the geometric stalk. -/
noncomputable def discretePi1ModuleOfFiniteTypeLocallyConstantSheaf (Λ : Type (u + 1)) [Ring Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [IrreducibleSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    DiscreteModuleCat Λ (Aut (standardFiniteEtaleFiber xbar)) :=
  ⟨{ V := étaleModuleStalk₁ Λ xbar F.obj, ρ := pi1HomOnEtaleModuleStalk Λ xbar F },
    fun _ ↦ sorry⟩

/-- The comparison object of a finite-type locally constant étale sheaf of `Λ`-modules
as a finite-type discrete `π₁`-module. -/
noncomputable def finitePi1ModuleOfFiniteTypeLocallyConstantSheaf (Λ : Type (u + 1)) [Ring Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [IrreducibleSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory :=
  ⟨discretePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F, sorry⟩

/-- The comparison functor sending a finite-type locally constant étale sheaf of
`Λ`-modules to its finite-type discrete `π₁`-module. -/
noncomputable def finiteTypeLocallyConstantModuleToFinitePi1Modules (Λ : Type (u + 1)) [Ring Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [IrreducibleSpace X] (huni : X.isGeometricallyUnibranch)
    (xbar : GeometricPoint X) :
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ⥤
      (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory where
  obj F := finitePi1ModuleOfFiniteTypeLocallyConstantSheaf Λ xbar F
  map {F G} f :=
    ObjectProperty.homMk <| ObjectProperty.homMk
      { hom := étaleModuleStalk₁Map Λ xbar f.hom
        comm := fun _ ↦ sorry }

/-- The finite-type `Λ`-module comparison functor is an equivalence. -/
noncomputable instance finiteTypeLocallyConstantModuleToFinitePi1Modules_isEquivalence
    (Λ : Type (u + 1)) [Ring Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [IrreducibleSpace X] (huni : X.isGeometricallyUnibranch)
    (xbar : GeometricPoint X) :
    (finiteTypeLocallyConstantModuleToFinitePi1Modules Λ huni xbar).IsEquivalence := sorry

/-- Finite-type locally constant étale sheaves of `Λ`-modules on an irreducible
geometrically unibranch scheme are equivalent to finite-type discrete `π₁`-modules. -/
noncomputable def finiteTypeLocallyConstantModule_equivalence_finitePi1Modules
    (Λ : Type (u + 1)) [Ring Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [IrreducibleSpace X] (huni : X.isGeometricallyUnibranch)
    (xbar : GeometricPoint X) :
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ≌
      (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory :=
  (finiteTypeLocallyConstantModuleToFinitePi1Modules Λ huni xbar).asEquivalence

/-- The module-valued equivalence sends a finite-type locally constant sheaf to a
finite-type discrete `π₁`-module. -/
theorem finiteTypePi1Modules_functor_obj (Λ : Type (u + 1)) [Ring Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [IrreducibleSpace X] (huni : X.isGeometricallyUnibranch)
    (xbar : GeometricPoint X)
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    IsFiniteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))
      ((finiteTypeLocallyConstantModule_equivalence_finitePi1Modules Λ huni xbar).functor.obj
        F).obj :=
  sorry

end AlgebraicGeometry.Scheme
