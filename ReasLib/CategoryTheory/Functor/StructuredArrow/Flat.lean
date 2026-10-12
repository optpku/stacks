/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import ReasLib.CategoryTheory.Filtered.ParallelPairCocones
public import ReasLib.CategoryTheory.Filtered.SpanCocones
import Mathlib.Tactic.CrossRefAttribute

/-!
# Filteredness properties of opposite structured-arrow categories

This module records the weak-cocone and filteredness consequences of finite
limit hypotheses for `StructuredArrow V u`. The weak-cocone classes are owned
by `ReasLib.CategoryTheory.Filtered`; this leaf only transports them through
the standard comma-category construction.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe uC vC uD vD

namespace CategoryTheory.StructuredArrow.Op

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- Lemma 7.5.1 (00X4): if `u` preserves pullbacks and equalizers, then the
opposite structured-arrow category has both span cocones and parallel-pair
cocones. The latter is the canonical class form of postcomposition
equalizers. -/
@[stacks 00X4]
theorem hasCocones
    (u : C ⥤ D) (V : D)
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u] :
    HasSpanCocones (StructuredArrow V u)ᵒᵖ ∧
      HasParallelPairCocones (StructuredArrow V u)ᵒᵖ := sorry

/-- The opposite structured-arrow category of a representably flat functor
is filtered. -/
theorem isFiltered
    (u : C ⥤ D) (V : D) [RepresentablyFlat u] :
    IsFiltered (StructuredArrow V u)ᵒᵖ := sorry

/-- Lemma 7.5.2 (00X3): an explicit terminal object whose image is terminal,
together with pullback preservation, makes the opposite structured-arrow
category filtered. -/
@[stacks 00X3]
theorem isFilteredOfTerminalAndPullbacks
    (u : C ⥤ D) (V : D) (X : C)
    (hX : IsTerminal X) (huX : IsTerminal (u.obj X))
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] :
    IsFiltered (StructuredArrow V u)ᵒᵖ := sorry

section

variable (u : C ⥤ D) (V : D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

#synth HasSpanCocones (StructuredArrow V u)ᵒᵖ
#synth HasParallelPairCocones (StructuredArrow V u)ᵒᵖ

end

section

variable (u : C ⥤ D) (V : D) [RepresentablyFlat u]

#synth IsFiltered (StructuredArrow V u)ᵒᵖ

end

end CategoryTheory.StructuredArrow.Op
