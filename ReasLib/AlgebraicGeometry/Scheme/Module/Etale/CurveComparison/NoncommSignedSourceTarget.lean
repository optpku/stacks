module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommSourceTarget
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommResidualDualComplex

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace NoncommSignedSourceTarget
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (η : GeometricPoint (geometricBaseChange X))
variable (hR : IsUnit (Nat.card R : k))
variable (M : (finiteTypeDiscreteModule R
  (Aut (standardFiniteEtaleFiber (arithmeticPoint X η)))).FullSubcategory)

/-- Signed character reversal of the SAME ambient injective resolution used
by the compact projective tensor model. -/
def residualCochain := NoncommResidualDualComplex.signedCharacterCochain Rᵐᵒᵖ
  (Aut (standardFiniteEtaleFiber η))
  (Aut (standardFiniteEtaleFiber (arithmeticPoint X η))) (NoncommSourceTarget.residualGroup X η)
  (geometricToArithmetic X η).hom (arithmeticToGalois X (arithmeticPoint X η)).hom
  (geometricToArithmetic_range_eq_arithmeticToGalois_ker X η)
  (arithmeticToGalois_surjective X (arithmeticPoint X η))
  (NoncommArithmeticTate.compactInput R X η hR M)

/-- Explicit phase/restriction/tensor comparison before coefficient normalization. -/
def residualIso : residualCochain R X η hR M ≅ NoncommSourceTarget.residualCochain R X η hR M :=
  NoncommResidualDualComplex.tensorIso Rᵐᵒᵖ
    (Aut (standardFiniteEtaleFiber η))
    (Aut (standardFiniteEtaleFiber (arithmeticPoint X η))) (NoncommSourceTarget.residualGroup X η)
    (geometricToArithmetic X η).hom (arithmeticToGalois X (arithmeticPoint X η)).hom
    (geometricToArithmetic_range_eq_arithmeticToGalois_ker X η)
    (arithmeticToGalois_surjective X (arithmeticPoint X η))
    (NoncommArithmeticTate.compactInput R X η hR M)

def normalizedCochain :=
  ((NoncommCompletedTransport.doubleOppositeModules R
    (G := NoncommSourceTarget.residualGroup X η)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (residualCochain R X η hR M)

def galoisCochain := ((NoncommSourceTarget.toGaloisModules R X η).mapHomologicalComplex
  (ComplexShape.up ℤ)).obj (normalizedCochain R X η hR M)

/-- Normalize opposite scalars and residual naming on the specified comparison. -/
def cochainIso : galoisCochain R X η hR M ≅ NoncommSourceTarget.galoisCochain R X η hR M :=
  ((NoncommSourceTarget.toGaloisModules R X η).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
    (((NoncommCompletedTransport.doubleOppositeModules R
      (G := NoncommSourceTarget.residualGroup X η)).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (residualIso R X η hR M))

variable [HasDerivedCategory (ModuleCat.{u + 1}
  (NoncommCompletedRing.Obj R Gal(AlgebraicClosure k/k)))]

/-- Integrated signed-character endpoint to the existing full noncommutative
derived completed-tensor target. No geometric comparison is assumed here. -/
def derivedIso : DerivedCategory.Q.obj (galoisCochain R X η hR M) ≅
    NoncommSourceTarget.derivedTarget R X η hR M :=
  DerivedCategory.Q.mapIso (cochainIso R X η hR M)

end NoncommSignedSourceTarget
