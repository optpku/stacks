module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Principal
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Chart
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field
public import Mathlib.Algebra.Field.Defs

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLine

variable (k : Type u) [Field k]

/-- The projective line over a field is integral. -/
instance scheme_isIntegral : IsIntegral (scheme k) := sorry

/-- The projective line over a field is locally Noetherian. -/
instance scheme_isLocallyNoetherian : IsLocallyNoetherian (scheme k) := sorry

/-- The standard zero point lies in the `X`-chart. -/
theorem zeroPoint_mem_chartX : zeroPoint k ∈ chartX k := sorry

/-- The standard `X`-chart is nonempty. -/
instance chartX_nonempty : Nonempty (chartX k) :=
  ⟨⟨zeroPoint k, zeroPoint_mem_chartX k⟩⟩

/-- The image of the affine coordinate `Y / X` in the function field is nonzero. -/
theorem coordinateFunctionValue_ne_zero :
    (scheme k).germToFunctionField (chartX k)
      ((XChart.sectionsComparison k) (XChart.coordinate k)) ≠ 0 := sorry

/-- The rational function `Y / X` on the projective line, with its zero at `0` and pole at `∞`. -/
noncomputable def coordinateFunction : (scheme k).functionFieldˣ :=
  Units.mk0
    ((scheme k).germToFunctionField (chartX k)
      ((XChart.sectionsComparison k) (XChart.coordinate k)))
    (coordinateFunctionValue_ne_zero k)

/-- The principal cycle of `Y / X` is the zero point minus the infinity point. -/
theorem principal_coordinateFunction :
    AlgebraicCycle.principal (scheme k) (coordinateFunction k) =
      @Function.locallyFinsuppWithin.single (scheme k) _ ℤ (Classical.decEq _) _
          (zeroPoint k) (1 : ℤ) -
        @Function.locallyFinsuppWithin.single (scheme k) _ ℤ (Classical.decEq _) _
          (infinityPoint k) (1 : ℤ) := sorry

/-- The reduced closure of the generic point maps its generic point back to the generic point. -/
theorem pointClosureι_map_genericPoint :
    (Scheme.PointClosure.ι (genericPoint (scheme k))).base
        (genericPoint (Scheme.PointClosure.scheme (genericPoint (scheme k)))) =
      genericPoint (scheme k) := sorry

/-- The function-field map from the projective line to the reduced closure of its generic point. -/
noncomputable def pointClosureFunctionFieldMap :
    (scheme k).functionField →+*
      (Scheme.PointClosure.scheme (genericPoint (scheme k))).functionField :=
  (Scheme.PointClosure.ι (genericPoint (scheme k))).functionFieldMap
    (pointClosureι_map_genericPoint k)

end AlgebraicGeometry.ProjectiveLine
