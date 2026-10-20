/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Homology
import StacksCheckRecall

/-!
# Definition 12.23.4

Source-facing checks for the filtration induced on homology by a filtered homological complex.
The shared owner is shape- and degree-polymorphic; the textbook differential object is its
one-object specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
variable (p : ℤ)

/- Definition 12.23.4 [012E]: the `p`-th stage of the induced filtration on `H(K)` is the
image of `H(F^p K) ⟶ H(K)`. -/
@[stacks 012E]
#check (HomologicalComplex.Filtered.Homology.Filtration.induced K PUnit.unit :
  DecreasingFiltration ((HomologicalComplex.Filtered.underlying K).homology PUnit.unit))

/- The defining stage formula is exposed separately for downstream calculations. -/
#check (HomologicalComplex.Filtered.Homology.Filtration.induced_stage K PUnit.unit p :
  (HomologicalComplex.Filtered.Homology.Filtration.induced K PUnit.unit).stage p =
    imageSubobject (HomologicalComplex.Filtered.Homology.map K p PUnit.unit))

/- The construction itself is available for arbitrary complex shapes and homology degrees. -/
#check HomologicalComplex.Filtered.Stage.complex
#check HomologicalComplex.Filtered.Stage.inclusion
#check HomologicalComplex.Filtered.Homology.map
#check HomologicalComplex.Filtered.Homology.map_naturality
