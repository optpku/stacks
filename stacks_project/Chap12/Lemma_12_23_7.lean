/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Filtration.DifferentialObject
import StacksCheckRecall

/-!
# Lemma 12.23.7

The main statements remain at the level of an arbitrary abelian category.  The optional
`ModuleCat` bridge realizes the same criteria as explicit submodule formulas without introducing
parallel convergence owners.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
variable [LocallySmall.{v} C] [WellPowered.{v} C]
  [HasWidePullbacks.{v} C] [HasCoproducts.{v} C]

/- Lemma 12.23.7 (1) [012J]: under complete subobject lattices, the canonical
weak-convergence representative criterion is the formal expression of the two pagewise
equalities, and it agrees with the explicit-representative core. -/
@[stacks 012J]
#check (HomologicalComplex.Filtered.Homology.Convergence.IsWeak K : Prop)
#check (HomologicalComplex.Filtered.Homology.Representative.IsWeak K : Prop)
#check HomologicalComplex.Filtered.Homology.Representative.IsWeak.boundary_eq
#check HomologicalComplex.Filtered.Homology.Representative.IsWeak.cycle_eq
#check HomologicalComplex.Filtered.Homology.Representative.IsWeak.of_equalities
#check HomologicalComplex.Filtered.Homology.Representative.IsWeak.iff_convergence
#check HomologicalComplex.Filtered.Homology.Convergence.Abuts.isWeak
#check HomologicalComplex.Filtered.Homology.Convergence.Abuts.isSeparatedExhaustive

/- Lemma 12.23.7 (2) [012J]: abutment is weak convergence together with the representative
intersection-and-union criterion for the induced homology filtration. -/
@[stacks 012J]
#check (HomologicalComplex.Filtered.Homology.Convergence.abuts_iff K :
  HomologicalComplex.Filtered.Homology.Convergence.Abuts K ↔
    HomologicalComplex.Filtered.Homology.Convergence.IsWeak K ∧
      HomologicalComplex.Filtered.Homology.Filtration.criterion K)
#check (HomologicalComplex.Filtered.Homology.Representative.IsWeak.abuts_iff K :
  HomologicalComplex.Filtered.Homology.Convergence.Abuts K ↔
    HomologicalComplex.Filtered.Homology.Representative.IsWeak K ∧
      HomologicalComplex.Filtered.Homology.Filtration.criterion K)

/- The source-independent concrete realization for filtered differential modules. -/
#check ModuleCat.FilteredDifferentialObject.ofLinearMap
#check ModuleCat.FilteredDifferentialObject.Homology.Convergence.isWeak_iff
#check ModuleCat.FilteredDifferentialObject.Homology.Convergence.abuts_iff
