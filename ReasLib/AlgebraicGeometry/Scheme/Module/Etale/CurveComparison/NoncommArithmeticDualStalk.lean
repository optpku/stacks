/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommIntrinsicDualStalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommCharacterRoots
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommArithmeticDualCoefficient

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace NoncommArithmeticDualStalk
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (η : GeometricPoint (geometricBaseChange X))
variable [X.left.smallEtaleTopology.HasSheafCompose (NoncommFiniteCoefficient.modules R)]
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} R)]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)]
variable [HasWeakSheafify X.left.smallEtaleTopology
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R)))]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U)
  (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card R)))]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable (hR : IsUnit (Nat.card R : k))
variable (M : (finiteTypeDiscreteModule R
  (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))).FullSubcategory)

/-- Actual finite arithmetic coefficient from the published inverse. -/
abbrev sourceSheaf :=
  ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules
    R (arithmeticPoint X η)).inverse.obj M).obj

/-- The geometric base change only supplies the specified embedding of kbar
into the point's field. The sheaf germ itself remains on arithmetic X. -/
abbrev geometricModel : SchemeOverField (AlgebraicClosure k) :=
  Over.mk (FieldExtension.toBase k (AlgebraicClosure k) X.hom)

/-- This model has the same underlying geometric base-change space. -/
instance geometricModel_connected : ConnectedSpace (geometricModel X).left :=
  inferInstanceAs (ConnectedSpace (geometricBaseChange X))

/-- The exact intrinsic local-Hom dual, with roots on arithmetic X. -/
abbrev dualA := NoncommFiniteCoefficient.dual R X.left (sourceSheaf R X η M)

/-- Evaluate a local-Hom germ on the published linear stalk counit, evaluate
the roots germ, then use the specified primitive-root character coordinate. -/
def toCharacter :
    (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} (Nat.card R)) (arithmeticPoint X η)).obj
      (dualA R X η M) →+ CharacterModule M.obj.obj.V where
  toFun α :=
    { toFun := fun m ↦ NoncommCharacterRoots.rootCharacter R hR
        ((NoncommIntrinsicDualStalk.rootsEquiv (geometricModel X) η (Nat.card R)
            (NoncommFiniteCoefficient.card_pos R)).symm
          (ActualRootsStalk.map (arithmeticPoint X η) (Nat.card R)
            ((ActualLinearHomStalk.map (ActualRootsModule.Coeff.{u} (Nat.card R))
              (arithmeticPoint X η)
              ((NoncommFiniteCoefficient.sheaves R X.left).obj (sourceSheaf R X η M))
              (ActualRootsModule.liftedSheaf X.left (Nat.card R)) α)
                ((NoncommIntrinsicDualStalk.scalarStalkIso X (arithmeticPoint X η) R
                    (sourceSheaf R X η M)).inv
                  ((ModuleSheafInverse.counitLinearEquiv (arithmeticPoint X η) R M).symm m)))))
      map_zero' := by sorry
      map_add' := by sorry }
  map_zero' := by sorry
  map_add' := by sorry

/-- Bijectivity concerns precisely the displayed germ/counit/root map. -/
theorem toCharacter_bijective : Function.Bijective (toCharacter R X η hR M) := by sorry

/-- The actual arithmetic stalk character equivalence, before coefficient rebundling. -/
def characterEquiv := AddEquiv.ofBijective (toCharacter R X η hR M)
  (toCharacter_bijective R X η hR M)

end NoncommArithmeticDualStalk
