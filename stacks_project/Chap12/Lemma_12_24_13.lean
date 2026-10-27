/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.ConvergenceCriteria
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

/- Lemma 12.24.13 hypotheses [0BK5]: stage cohomology eventually vanishes above and stabilizes
below. -/
#check FilteredComplex.StageCohomology.eventuallyVanishesAbove
#check FilteredComplex.StageCohomology.eventuallyStabilizesBelow

/- Standard acyclicity and quasi-isomorphism formulations imply the stagewise criteria. -/
#check FilteredComplex.StageCohomology.eventuallyVanishesAbove_of_acyclic
#check FilteredComplex.StageCohomology.eventuallyStabilizesBelow_of_quasiIso

/- Lemma 12.24.13 (1) [0BK5]: the page-one tail of every associated spectral sequence is bounded. -/
@[stacks 0BK5]
#check (FilteredComplex.StageCohomology.associated_isBounded :
  ∀ {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0),
    FilteredComplex.IsAssociated K E →
      FilteredComplex.StageCohomology.eventuallyVanishesAbove K →
        FilteredComplex.StageCohomology.eventuallyStabilizesBelow K →
          CohomologicalSpectralSequence.IsBounded
            (CohomologicalSpectralSequence.Page.One.ofZero E))

/- Lemma 12.24.13 (2) [0BK5]: every induced cohomology filtration is finite. -/
@[stacks 0BK5]
#check (FilteredComplex.StageCohomology.Cohomology.isFinite :
  ∀ {C : Type u} [Category.{v} C] [Abelian C] (K : FilteredComplex C),
    FilteredComplex.StageCohomology.eventuallyVanishesAbove K →
      FilteredComplex.StageCohomology.eventuallyStabilizesBelow K →
        FilteredComplex.Cohomology.Filtration.IsFinite K)

/- Lemma 12.24.13 (3) [0BK5]: every associated spectral sequence converges to cohomology. -/
@[stacks 0BK5]
#check (FilteredComplex.StageCohomology.associated_converges :
  ∀ {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C) (E : CohomologicalSpectralSequence C 0),
    FilteredComplex.IsAssociated K E →
      FilteredComplex.StageCohomology.eventuallyVanishesAbove K →
        FilteredComplex.StageCohomology.eventuallyStabilizesBelow K →
          FilteredComplex.Cohomology.Convergence.Converges K E)
