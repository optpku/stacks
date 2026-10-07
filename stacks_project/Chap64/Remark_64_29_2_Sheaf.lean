module

public import ReasLib.CategoryTheory.Action.ModuleCat.OpenStabilizer.Definition
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Lemma_59_65_1_Equivalence
public import stacks_project.Chap59.Remark_59_65_3

/-!
# Locally constant sheaf attached to a finite discrete π₁-module

This leaf owns the sheaf `F_ρ` associated with a finite discrete continuous
`π₁`-module, as the inverse of the finite-type locally constant comparison of
Lemma 59.65.1.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Action.ModuleCat
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [ConnectedSpace X]
variable (xbar : GeometricPoint X)
variable (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- The finite-type locally constant étale sheaf of `Λ`-modules associated with a finite
discrete continuous `π₁(X, x̄)`-module. -/
def sheafOfPi1Module
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).inverse.obj M).obj

/-- The associated sheaf is the underlying object of the inverse comparison functor. -/
theorem sheafOfPi1Module_eq
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    sheafOfPi1Module xbar Λ M =
      ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ
          xbar).inverse.obj M).obj :=
  sorry

/-- The sheaf associated with a finite discrete `π₁`-module is locally constant of finite
type. -/
instance sheafOfPi1Module_isFiniteTypeLocallyConstant
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    Sheaf.IsFiniteTypeLocallyConstantModule (sheafOfPi1Module xbar Λ M) :=
  ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).inverse.obj
      M).property

/-- Applying the finite-type comparison functor to `sheafOfPi1Module` recovers the original
discrete `π₁`-module. -/
def sheafOfPi1Module_counit
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).functor.obj
        ⟨sheafOfPi1Module xbar Λ M, sheafOfPi1Module_isFiniteTypeLocallyConstant xbar Λ M⟩ ≅
      M :=
  (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).counitIso.app M

/-- The counit of the locally constant comparison at `sheafOfPi1Module` is the comparison
counit at `M`. -/
theorem sheafOfPi1Module_counit_eq
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    sheafOfPi1Module_counit xbar Λ M =
      (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ
          xbar).counitIso.app M :=
  sorry

/-- A morphism of finite discrete `π₁`-modules induces a morphism of the associated
locally constant sheaves. -/
def sheafOfPi1Module_map
    {M N : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory}
    (f : M ⟶ N) :
    sheafOfPi1Module xbar Λ M ⟶ sheafOfPi1Module xbar Λ N :=
  ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).inverse.map f).hom

/-- `sheafOfPi1Module_map` is the underlying sheaf morphism of the inverse comparison
functor. -/
theorem sheafOfPi1Module_map_eq
    {M N : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory}
    (f : M ⟶ N) :
    sheafOfPi1Module_map xbar Λ f =
      ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ
          xbar).inverse.map f).hom :=
  sorry

/-- The associated sheaf is finite-type locally constant, and the comparison functor recovers
the original discrete module. -/
theorem sheafOfPi1Module_spec
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    Sheaf.IsFiniteTypeLocallyConstantModule (sheafOfPi1Module xbar Λ M) ∧
      Nonempty
        ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).functor.obj
            ⟨sheafOfPi1Module xbar Λ M,
              sheafOfPi1Module_isFiniteTypeLocallyConstant xbar Λ M⟩ ≅
          M) :=
  sorry

/-- Restriction of a finite-type discrete `π₁(X)`-module along a morphism of connected
schemes, as a finite-type discrete `π₁(Y)`-module. -/
def geometricPi1Module {Y : Scheme.{u}} [ConnectedSpace Y] (f : Y ⟶ X)
    (ybar : GeometricPoint Y)
    (M : (finiteTypeDiscreteModule Λ
        (Aut (standardFiniteEtaleFiber (geometricPointPostcomp ybar f)))).FullSubcategory) :
    (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber ybar))).FullSubcategory :=
  (etaleFundamentalGroupMap_resFiniteTypeDiscreteModule f Λ ybar).obj M

/-- Unfolding of restriction of finite-type discrete `π₁`-modules along `f`. -/
theorem geometricPi1Module_eq {Y : Scheme.{u}} [ConnectedSpace Y] (f : Y ⟶ X)
    (ybar : GeometricPoint Y)
    (M : (finiteTypeDiscreteModule Λ
        (Aut (standardFiniteEtaleFiber (geometricPointPostcomp ybar f)))).FullSubcategory) :
    geometricPi1Module Λ f ybar M =
      (etaleFundamentalGroupMap_resFiniteTypeDiscreteModule f Λ ybar).obj M :=
  sorry

end AlgebraicGeometry.Scheme
