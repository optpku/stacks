/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteDualStalkComparison

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace ActualFiniteDualComparison
variable {k : Type u} [Field k]
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (X : SchemeOverField k) [ConnectedSpace (geometricBaseChange X)]
variable (ηbar : GeometricPoint (geometricBaseChange X))

variable [(geometricBaseChange X).smallEtaleTopology.HasSheafCompose (ActualFiniteCoefficient.modules Λ)]
variable [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : (geometricBaseChange X).Etale,
    HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify (geometricBaseChange X).smallEtaleTopology
    (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]
variable [∀ U : (geometricBaseChange X).Etale,
    HasWeakSheafify ((geometricBaseChange X).smallEtaleTopology.over U)
      (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]
variable [HasSheafify (geometricBaseChange X).smallEtaleTopology AddCommGrpCat.{u + 1}]
variable (hΛ : IsUnit (Nat.card Λ : k))
variable (M : (finiteTypeDiscreteModule Λ (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))).FullSubcategory)

/-- The actual contragredient action on the ordinary character module. -/
def characterAction : Action (ModuleCat.{u + 1} Λ) (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) where
  V := ModuleCat.of Λ (CharacterModule M.obj.obj.V)
  ρ := { toFun := fun γ ↦ ModuleCat.ofHom (CharacterModule.dual (M.obj.obj.ρ γ⁻¹).hom)
         map_one' := sorry
         map_mul' := sorry }

/-- Include the same finite character action with its Z/(card Lambda) scalars. -/
def characterRepresentation :
    (finiteTypeDiscreteModule (ActualRootsModule.Coeff.{u} (Nat.card Λ))
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))).FullSubcategory :=
  ⟨⟨((ActualFiniteCoefficient.modules Λ).mapAction
      (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar))).obj (characterAction Λ X ηbar M), by sorry⟩, by sorry⟩

include hΛ in
/-- The intrinsic dual is finite locally constant because roots of unity
have invertible finite order and the source is a finite local system. -/
theorem dualSheaf_finite :
    Sheaf.IsFiniteTypeLocallyConstantModule (dualSheaf Λ X ηbar M) := sorry

def finiteDualSheaf :
    (Sheaf.finiteTypeLocallyConstantModule (geometricBaseChange X).smallEtaleTopology
      (ActualRootsModule.Coeff.{u} (Nat.card Λ))).FullSubcategory :=
  ⟨dualSheaf Λ X ηbar M, dualSheaf_finite Λ X ηbar hΛ M⟩

/-- The linear stalk comparison has the already specified germ/counit map. -/
def stalkLinearEquiv :
    (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} (Nat.card Λ)) ηbar).obj
      (dualSheaf Λ X ηbar M) ≃ₗ[ActualRootsModule.Coeff.{u} (Nat.card Λ)]
    (characterRepresentation Λ X ηbar M).obj.obj.V where
  __ := stalkCharacterEquiv Λ X ηbar hΛ M
  map_smul' := sorry

/-- Geometric monodromy on local Hom acts by precomposition on the source;
the roots values from the algebraically closed ground field are fixed. -/
theorem stalkLinearEquiv_equivariant (γ : Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber ηbar)) :
    ((finiteTypeLocallyConstantModuleToFinitePi1LambdaModules
      (ActualRootsModule.Coeff.{u} (Nat.card Λ)) ηbar).obj
      (finiteDualSheaf Λ X ηbar hΛ M)).obj.obj.ρ γ ≫
        (stalkLinearEquiv Λ X ηbar hΛ M).toModuleIso.hom =
    (stalkLinearEquiv Λ X ηbar hΛ M).toModuleIso.hom ≫
      (characterRepresentation Λ X ηbar M).obj.obj.ρ γ := sorry

def stalkRepresentationIso :
    (finiteTypeLocallyConstantModuleToFinitePi1LambdaModules
      (ActualRootsModule.Coeff.{u} (Nat.card Λ)) ηbar).obj
      (finiteDualSheaf Λ X ηbar hΛ M) ≅ characterRepresentation Λ X ηbar M :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (Action.mkIso (stalkLinearEquiv Λ X ηbar hΛ M).toModuleIso
      (stalkLinearEquiv_equivariant Λ X ηbar hΛ M)))

/-- The full sheaf comparison is the PUBLISHED concrete sheaf unit followed
by its inverse functor applied to the specified equivariant stalk map. -/
def sheafIso :
    dualSheaf Λ X ηbar M ≅
    (associatedSheafFunctor (ActualRootsModule.Coeff.{u} (Nat.card Λ)) ηbar).obj
      (characterRepresentation Λ X ηbar M) :=
  (Sheaf.finiteTypeLocallyConstantModule (geometricBaseChange X).smallEtaleTopology
    (ActualRootsModule.Coeff.{u} (Nat.card Λ))).ι.mapIso
      (((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules
        (ActualRootsModule.Coeff.{u} (Nat.card Λ)) ηbar).unitIso.app
          (finiteDualSheaf Λ X ηbar hΛ M)) ≪≫
        (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules
          (ActualRootsModule.Coeff.{u} (Nat.card Λ)) ηbar).inverse.mapIso
            (stalkRepresentationIso Λ X ηbar hΛ M))

end ActualFiniteDualComparison
