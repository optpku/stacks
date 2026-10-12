/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommSourceTarget

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace NoncommTensorNaturality
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (η : GeometricPoint (geometricBaseChange X))
variable (hR : IsUnit (Nat.card R : k))

abbrev Input := (finiteTypeDiscreteModule R
  (Aut (standardFiniteEtaleFiber (arithmeticPoint X η)))).FullSubcategory

/-- The inverse Tate functor preserves the given coefficient map. Scalars are
transported through the specified double opposite, never commuted. -/
def compactInputMap {M N : Input R X η} (f : M ⟶ N) :
    NoncommArithmeticTate.compactInput R X η hR M ⟶ NoncommArithmeticTate.compactInput R X η hR N :=
  ObjectProperty.homMk
    { hom :=
        { toLinearMap :=
            { toFun := fun m ↦ f.hom.hom.hom.hom m
              map_add' := by sorry
              map_smul' := by sorry }
          cont := by sorry }
      comm := fun _ ↦ by sorry }

abbrev tensorFunctor := NoncommDerivedTensor.tensorFunctor Rᵐᵒᵖ
  (Aut (standardFiniteEtaleFiber η))
  (Aut (standardFiniteEtaleFiber (arithmeticPoint X η))) (NoncommSourceTarget.residualGroup X η)
  (geometricToArithmetic X η).hom (arithmeticToGalois X (arithmeticPoint X η)).hom
  (geometricToArithmetic_range_eq_arithmeticToGalois_ker X η)
  (arithmeticToGalois_surjective X (arithmeticPoint X η))

abbrev resolution (M : Input R X η) := NoncommDualResolution.chosen Rᵐᵒᵖ
  (Aut (standardFiniteEtaleFiber (arithmeticPoint X η))) (NoncommArithmeticTate.compactInput R X η hR M)

/-- Use the actual recursive projective lift between the SAME chosen compact
resolutions. Functoriality holds after homotopy/localization. -/
def residualMap {M N : Input R X η} (f : M ⟶ N) :
    NoncommSourceTarget.residualCochain R X η hR M ⟶ NoncommSourceTarget.residualCochain R X η hR N :=
  HomologicalComplex.extendMap
    (((tensorFunctor R X η ⋙ NoncommCompletedAction.functor Rᵐᵒᵖᵐᵒᵖ
      (NoncommSourceTarget.residualGroup X η)).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift (compactInputMap R X η hR f)
          (resolution R X η hR M) (resolution R X η hR N))) CompactRepresentation.curveDegreeEmbedding

/-- The same map with original coefficient handedness and field-Galois naming. -/
def map {M N : Input R X η} (f : M ⟶ N) :
    NoncommSourceTarget.galoisCochain R X η hR M ⟶ NoncommSourceTarget.galoisCochain R X η hR N :=
  ((NoncommSourceTarget.toGaloisModules R X η).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (((NoncommCompletedTransport.doubleOppositeModules R
      (G := NoncommSourceTarget.residualGroup X η)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (residualMap R X η hR f))

variable [HasDerivedCategory (ModuleCat.{u + 1}
  (NoncommCompletedRing.Obj R Gal(AlgebraicClosure k/k)))]

/-- Full target functor on finite source coefficients, derived using ambient
compact projectives. Identity/composition are the actual lift homotopies. -/
def derivedFunctor : Input R X η ⥤ DerivedCategory
    (ModuleCat.{u + 1} (NoncommCompletedRing.Obj R Gal(AlgebraicClosure k/k))) where
  obj M := NoncommSourceTarget.derivedTarget R X η hR M
  map f := DerivedCategory.Q.map (map R X η hR f)
  map_id := by sorry
  map_comp := by sorry

end NoncommTensorNaturality
