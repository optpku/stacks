module

public import stacks_project.Chap59.Lemma_59_65_1_Forward
public import stacks_project.Chap59.Lemma_59_65_1_StalkComparison

/-!
# Finite module-sheaf equivalence with the published forward functor

The inverse uses transported module operations on the set-level inverse. Its
unit and counit use the specified germ and finite-set comparison maps.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The finite-type `Λ`-module comparison functor is an equivalence. -/
noncomputable instance finiteTypeLocallyConstantModuleToFinitePi1LambdaModules_isEquivalence
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X) :
    (finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).IsEquivalence :=
  (ModuleSheafInverse.equivalence xbar Λ).isEquivalence_functor

/-- Finite-type locally constant étale sheaves of `Λ`-modules, for a finite ring `Λ`, are
equivalent to finite discrete `π₁`-modules with commuting `Λ`-action. -/
noncomputable def finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X) :
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ≌
      (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory :=
  ModuleSheafInverse.equivalence xbar Λ

/-- The module-valued equivalence sends a finite-type locally constant sheaf to a finite-type
discrete `π₁`-module. -/
theorem finiteTypePi1LambdaModules_functor_obj
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    IsFiniteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))
      ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).functor.obj
        F).obj :=
  sorry

end AlgebraicGeometry.Scheme
