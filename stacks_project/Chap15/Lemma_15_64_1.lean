/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.ConvergenceCriteria
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.64.1 (0H7W)

The source Kunneth spectral sequence is the associated spectral sequence of the filtered tensor
model. Its two eventual stage hypotheses are converted to the canonical stage-cohomology
conditions, after which boundedness, finite induced cohomology filtrations, and convergence are
exactly the shared `FilteredComplex.StageCohomology` API.

@stack 0H7W
-/

open CategoryTheory

/- Lemma 15.64.1: eventual acyclicity of high stages gives eventual cohomology vanishing. -/
@[stacks 0H7W "Lemma 15.64.1, high-stage acyclicity"]
#check @FilteredComplex.StageCohomology.eventuallyVanishesAbove_of_acyclic

/- Lemma 15.64.1: eventual quasi-isomorphism of low stages gives cohomology stabilization. -/
@[stacks 0H7W "Lemma 15.64.1, low-stage stabilization"]
#check @FilteredComplex.StageCohomology.eventuallyStabilizesBelow_of_quasiIso

/- Lemma 15.64.1: the associated spectral sequence is bounded. -/
@[stacks 0H7W "Lemma 15.64.1, boundedness"]
#check @FilteredComplex.StageCohomology.associated_isBounded

/- Lemma 15.64.1: the induced cohomology filtrations are finite. -/
@[stacks 0H7W "Lemma 15.64.1, finite cohomology filtration"]
#check @FilteredComplex.StageCohomology.Cohomology.isFinite

/- Lemma 15.64.1: the associated spectral sequence converges to filtered-complex cohomology. -/
@[stacks 0H7W "Lemma 15.64.1, convergence"]
#check @FilteredComplex.StageCohomology.associated_converges

/- The finite-filtration specialization in Lemma 15.64.1. -/
@[stacks 0H7W "Lemma 15.64.1, finite-filtration specialization"]
#check @FilteredComplex.HasFiniteFiltrations.Convergence.converges
