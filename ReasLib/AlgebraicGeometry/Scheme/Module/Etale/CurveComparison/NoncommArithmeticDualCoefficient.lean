module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommArithmeticTate
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.OppositeFiniteCharacterSheaf

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace NoncommArithmeticDualCoefficient
variable {k : Type u} [Field k]
variable (R : Type (u + 1)) [Ring R] [Finite R]
variable (X : SchemeOverField k)
variable [ConnectedSpace X.left] [ConnectedSpace (geometricBaseChange X)]
variable [ConnectedSpace (Spec (CommRingCat.of k))]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (η : GeometricPoint (geometricBaseChange X))
variable (hR : IsUnit (Nat.card R : k))
variable (M : (finiteTypeDiscreteModule R
  (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))).FullSubcategory)

/-- The inverse twist retains the actual finite-type coefficient module. -/
def finiteTwist : (finiteTypeDiscreteModule R
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))).FullSubcategory :=
  ⟨NoncommArithmeticTate.inverseTwist R X η hR M.obj, M.property⟩

/-- The actual RIGHT R coefficient of the dual sheaf. Dualizing M(-1)
produces the positive cyclotomic action required by the source. -/
def representation := ActualOppositeCharacter.finiteRepresentation R
  (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η))) (finiteTwist R X η hR M)

variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} Rᵐᵒᵖ)]

/-- The associated right-coefficient character/Tate sheaf, with published module operations. -/
def sheaf :=
  (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules
    Rᵐᵒᵖ (arithmeticPoint X η)).inverse.obj (representation R X η hR M)

/-- Its stalk is identified by the actual published linear equivariant counit. -/
def stalkIso :=
  (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules
    Rᵐᵒᵖ (arithmeticPoint X η)).counitIso.app (representation R X η hR M)

end NoncommArithmeticDualCoefficient
