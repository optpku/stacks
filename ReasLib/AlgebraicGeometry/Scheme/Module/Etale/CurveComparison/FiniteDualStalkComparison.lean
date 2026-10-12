/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.IntrinsicDualStalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CharacterRootsCoefficient

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

abbrev geometricCurve : SchemeOverField (AlgebraicClosure k) :=
  Over.mk (FieldExtension.toBase k (AlgebraicClosure k) X.hom)

instance geometricCurve_connected : ConnectedSpace (geometricCurve X).left :=
  inferInstanceAs (ConnectedSpace (geometricBaseChange X))

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
variable (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber ηbar))).FullSubcategory)

abbrev sourceSheaf := (associatedSheafFunctor Λ ηbar).obj M

instance sourceSheaf_finite : Sheaf.IsFiniteTypeLocallyConstantModule (sourceSheaf Λ X ηbar M) :=
  ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ ηbar).inverse.obj M).property

abbrev dualSheaf := ActualFiniteCoefficient.dual Λ (geometricBaseChange X) (sourceSheaf Λ X ηbar M)

/-- Evaluate the intrinsic dual stalk, use the published source stalk counit,
then convert the resulting root-valued function into its rational character. -/
def stalkToCharacter :
    (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} (Nat.card Λ)) ηbar).obj
      (dualSheaf Λ X ηbar M) →+ CharacterModule M.obj.obj.V where
  toFun α := ActualCharacterRoots.rootsToCharacter Λ hΛ M.obj.obj.V
    ((ActualIntrinsicDualStalk.map (geometricCurve X) ηbar Λ (sourceSheaf Λ X ηbar M) α).comp
      (ModuleSheafInverse.counitLinearEquiv ηbar Λ M).symm.toAddEquiv.toAddMonoidHom)
  map_zero' := sorry
  map_add' := sorry

/-- This is bijectivity of the actual germ/evaluation/counit map. -/
theorem stalkToCharacter_bijective : Function.Bijective (stalkToCharacter Λ X ηbar hΛ M) := sorry

def stalkCharacterEquiv :
    (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} (Nat.card Λ)) ηbar).obj
      (dualSheaf Λ X ηbar M) ≃+ CharacterModule M.obj.obj.V :=
  AddEquiv.ofBijective (stalkToCharacter Λ X ηbar hΛ M)
    (stalkToCharacter_bijective Λ X ηbar hΛ M)

/-- The comparison respects the original Lambda scalar action, represented
on the intrinsic dual by precomposition and on characters by evaluation. -/
theorem stalkToCharacter_scalar (a : Λ)
    (α : (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} (Nat.card Λ)) ηbar).obj
      (dualSheaf Λ X ηbar M)) :
    stalkToCharacter Λ X ηbar hΛ M
      ((StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} (Nat.card Λ)) ηbar).map
        (ActualFiniteCoefficient.dualScalarEnd Λ (geometricBaseChange X)
          (sourceSheaf Λ X ηbar M) a) α) =
      a • stalkToCharacter Λ X ηbar hΛ M α := sorry

end ActualFiniteDualComparison
