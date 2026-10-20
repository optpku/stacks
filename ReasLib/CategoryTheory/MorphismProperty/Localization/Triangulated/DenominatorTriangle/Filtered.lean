module

public import Mathlib.CategoryTheory.Filtered.Final
public import ReasLib.CategoryTheory.MorphismProperty.Localization.Triangulated.DenominatorTriangle.Rotation

/-!
# Filtered triangle-denominator categories

For a saturated multiplicative system compatible with the triangulation, the denominator
category under a distinguished triangle is filtered.  Each of its three vertex projections is
final.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory.MorphismProperty.TriangleDenominator

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable (W : MorphismProperty C) (T : Triangle C)

/-- If `W` contains identities, a distinguished source triangle has a canonical object in its
triangle-denominator category. -/
theorem nonempty [W.ContainsIdentities] (hT : T ∈ distTriang C) :
    Nonempty (TriangleDenominator W T) := sorry

variable [W.IsSaturatedMultiplicativeSystem] [W.IsCompatibleWithTriangulation]

/-- Stacks 05R9: the category of denominators under a distinguished triangle is filtered. -/
@[stacks 05R9 "filtered category of denominators under a distinguished triangle"]
theorem isFiltered (hT : T ∈ distTriang C) : IsFiltered (TriangleDenominator W T) := sorry

/-- Stacks 05R9: the first-vertex projection from triangle denominators is final. -/
@[stacks 05R9 "first final projection from triangle denominators"]
theorem projection₁_final (hT : T ∈ distTriang C) : (projection₁ W T).Final := sorry

/-- Stacks 05R9: the second-vertex projection from triangle denominators is final. -/
@[stacks 05R9 "second final projection from triangle denominators"]
theorem projection₂_final (hT : T ∈ distTriang C) : (projection₂ W T).Final := sorry

/-- Stacks 05R9: the third-vertex projection from triangle denominators is final. -/
@[stacks 05R9 "third final projection from triangle denominators"]
theorem projection₃_final (hT : T ∈ distTriang C) : (projection₃ W T).Final := sorry

end CategoryTheory.MorphismProperty.TriangleDenominator
