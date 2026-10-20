/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.HomologicalComplex.Convergence
import StacksCheckRecall

/-!
# Definition 12.23.6

Source-facing checks for weak convergence and abutment of a filtered differential object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

section Convergence

/- Definition 12.23.6 (1) [012I]: weak convergence is first expressed relative to explicit
eventual representatives, and unqualified weak convergence records their existence. -/
@[stacks 012I]
#check @HomologicalComplex.Filtered.Homology.Convergence.IsWeakAlong
#check (HomologicalComplex.Filtered.Homology.Convergence.IsWeak K : Prop)
#check HomologicalComplex.Filtered.Homology.Convergence.IsWeak.of_along
#check HomologicalComplex.Filtered.Homology.Convergence.IsWeak.exists_along

/- Definition 12.23.6 (2) [012I]: abutment has the same explicit-representative layer and is
weak convergence together with a separated and exhaustive induced filtration on homology. -/
@[stacks 012I]
#check @HomologicalComplex.Filtered.Homology.Convergence.AbutsAlong
#check (HomologicalComplex.Filtered.Homology.Convergence.Abuts K : Prop)
#check HomologicalComplex.Filtered.Homology.Convergence.Abuts.of_along
#check HomologicalComplex.Filtered.Homology.Convergence.Abuts.exists_along

end Convergence

/- The separated-and-exhaustive component of abutment remains directly consumable. -/
#check (HomologicalComplex.Filtered.Homology.Filtration.IsSeparatedExhaustive K : Prop)

section HomologyFiltration

variable [CompleteLattice
  (Subobject ((HomologicalComplex.Filtered.underlying K).homology PUnit.unit))]

/- Separatedness and exhaustiveness also have the expected complete-lattice formulation. -/
#check HomologicalComplex.Filtered.Homology.Filtration.isSeparatedExhaustive_iff

end HomologyFiltration
