/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap58.Lemma_58_14_3_Induced
public import stacks_project.Chap59.Lemma_59_65_1_Equivalence

/-!
# Locally constant sheaves associated to finite π₁-modules

This leaf owns the sheaf `F_ρ` associated to a finite discrete continuous `π₁`-module,
as the inverse of the finite-type locally constant / finite `π₁`-module equivalence.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}
variable (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [ConnectedSpace X]

/-- The functor sending a finite discrete `π₁`-module to the associated finite-type
locally constant étale sheaf of `Λ`-modules. -/
def associatedSheafFunctor (xbar : GeometricPoint X) :
    (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).inverse ⋙
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).ι

/-- The étale sheaf `F_ρ` associated to a finite discrete continuous `π₁(X, x̄)`-module. -/
def associatedSheaf (xbar : GeometricPoint X)
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (associatedSheafFunctor Λ xbar).obj M

/-- Unfolding of `associatedSheaf` as the underlying sheaf of the inverse equivalence. -/
theorem associatedSheaf_obj (xbar : GeometricPoint X)
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    associatedSheaf Λ xbar M =
      ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).inverse.obj
        M).obj :=
  sorry

/-- The sheaf associated to a finite discrete `π₁`-module is finite-type locally constant. -/
theorem associatedSheaf_spec (xbar : GeometricPoint X)
    (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory) :
    Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ (associatedSheaf Λ xbar M) :=
  sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.SchemeOverField

open AlgebraicGeometry.Scheme

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.left.Etale,
    HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]

/-- The étale sheaf on `X` associated to a finite discrete continuous module for the
arithmetic étale fundamental group at the image of a geometric point of `X_k̄`. -/
def associatedSheaf (ηbar : GeometricPoint (geometricBaseChange X))
    (M : (finiteTypeDiscreteModule Λ
        (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory) :
    Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  Scheme.associatedSheaf Λ (arithmeticPoint X ηbar) M

/-- Unfolding of the arithmetic associated sheaf as `Scheme.associatedSheaf` at the image
geometric point. -/
theorem associatedSheaf_obj (ηbar : GeometricPoint (geometricBaseChange X))
    (M : (finiteTypeDiscreteModule Λ
        (Aut (standardFiniteEtaleFiber (arithmeticPoint X ηbar)))).FullSubcategory) :
    associatedSheaf X Λ ηbar M = Scheme.associatedSheaf Λ (arithmeticPoint X ηbar) M :=
  sorry

end AlgebraicGeometry.SchemeOverField

