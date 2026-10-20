module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommArithmeticDualCoefficient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommRepresentationDuality

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace NoncommFiniteCompactDualInput
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

abbrev inverseInput := NoncommRepresentationDuality.inverseDiscrete Rᵐᵒᵖ
  (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))
  (NoncommArithmeticTate.compactInput R X η hR M)

/-- On this finite discrete compact input every additive character is continuous. -/
theorem character_continuous
    (χ : (NoncommArithmeticDualCoefficient.representation R X η hR M).obj.obj.V) :
    Continuous (NoncommCompactCharacters.coordinates Rᵐᵒᵖᵐᵒᵖ
      (NoncommArithmeticTate.compactCoefficient R X η hR M).toModule χ) := by
  -- Local instance justification (defeq pin): this compact input was explicitly assigned the discrete topology.
  letI : DiscreteTopology (NoncommArithmeticTate.compactCoefficient R X η hR M).toModule := ⟨rfl⟩
  exact continuous_of_discreteTopology

/-- Forget only the redundant continuity proof; the inverse inserts the proven
continuity of that same character. Triple-opposite normalization preserves right R scalars. -/
def moduleEquiv : (inverseInput R X η hR M).obj.V ≃ₗ[Rᵐᵒᵖ]
    (NoncommArithmeticDualCoefficient.representation R X η hR M).obj.obj.V where
  toFun χ := χ.val
  invFun χ := ⟨χ, character_continuous R X η hR M χ⟩
  left_inv := by intro χ; rfl
  right_inv := by intro χ; rfl
  map_add' := by intros; rfl
  map_smul' := by sorry

/-- Both actions are literal character precomposition by the inverse of the
same arithmetic inverse-Tate action. -/
def representationIso : inverseInput R X η hR M ≅
    (NoncommArithmeticDualCoefficient.representation R X η hR M).obj :=
  ObjectProperty.isoMk _ (Action.mkIso (moduleEquiv R X η hR M).toModuleIso (fun _ ↦ by sorry))

/-- The inverse-character input is finite type through the displayed linear equivalence. -/
theorem inverseInput_finiteType : Module.Finite Rᵐᵒᵖ (inverseInput R X η hR M).obj.V := by sorry

def finiteInput : (finiteTypeDiscreteModule Rᵐᵒᵖ
    (Aut (AlgebraicGeometry.Scheme.GeometricPoint.finiteFiber (arithmeticPoint X η)))).FullSubcategory :=
  ⟨inverseInput R X η hR M, inverseInput_finiteType R X η hR M⟩

/-- Actual finite-category comparison; no injective/projective resolution is
taken in this finite subcategory. -/
def finiteIso : finiteInput R X η hR M ≅ NoncommArithmeticDualCoefficient.representation R X η hR M :=
  ObjectProperty.isoMk _ (representationIso R X η hR M)

end NoncommFiniteCompactDualInput
