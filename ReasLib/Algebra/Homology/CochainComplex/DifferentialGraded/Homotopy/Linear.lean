/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Homotopy.Preadditive
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded

/-!
# Linear structure on enriched cochain homotopy categories

For a category `C` linear over a commutative ring `R`, the explicit differential graded
structure `CochainComplex.differentialGradedCategory C R` induces the canonical category,
preadditive, and `R`-linear structures on its homotopy category.

The base ring of `DifferentialGradedCategory` is an `outParam`, so its generic cochain-complex
instance must remain explicit.  The carrier `DifferentialGradedCategory.K R _` records `R`,
however, and therefore supports these coherent scoped instances without local instance pins.
-/

@[expose] public section

noncomputable section

universe r u v

open CategoryTheory

namespace CategoryTheory.CochainComplex.Enriched.Over

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The homotopy category of the explicit `R`-linear cochain-complex enrichment has its
canonical category structure. -/
@[reducible, stacks 09JQ "cochain homotopy category over a base ring"]
noncomputable scoped instance kCategory :
    Category (DifferentialGradedCategory.K R (CochainComplex C ℤ)) :=
  @DifferentialGradedCategory.kCategory R _ _
    (CochainComplex.differentialGradedCategory C R)

/-- The homotopy category of the explicit `R`-linear cochain-complex enrichment is
canonically preadditive. -/
@[reducible, stacks 09JQ "preadditive cochain homotopy category over a base ring"]
noncomputable scoped instance kPreadditive :
    Preadditive (DifferentialGradedCategory.K R (CochainComplex C ℤ)) :=
  @DifferentialGradedCategory.kPreadditive R _ _
    (CochainComplex.differentialGradedCategory C R)

/-- The homotopy category of the explicit `R`-linear cochain-complex enrichment is
canonically `R`-linear. -/
@[reducible, stacks 09JQ "linear cochain homotopy category over a base ring"]
noncomputable scoped instance kLinear :
    Linear R (DifferentialGradedCategory.K R (CochainComplex C ℤ)) :=
  @DifferentialGradedCategory.kLinear R _ _
    (CochainComplex.differentialGradedCategory C R)

end CategoryTheory.CochainComplex.Enriched.Over
