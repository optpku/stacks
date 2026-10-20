/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.Convergence.WeakSerre
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 12.24.11 (1) [012W]: finite term filtrations make an associated spectral sequence
bounded. -/
@[stacks 012W]
#check FilteredComplex.HasFiniteFiltrations.Convergence.isBounded_of_associated

/- Lemma 12.24.11 (2) [012W]: finite term filtrations induce finite filtrations on cohomology. -/
@[stacks 012W]
#check FilteredComplex.HasFiniteFiltrations.Cohomology.isFinite

/- Lemma 12.24.11 (3) [012W]: the associated spectral sequence of a termwise finitely filtered
complex converges to its cohomology. -/
@[stacks 012W]
#check FilteredComplex.HasFiniteFiltrations.Convergence.converges

/- Lemma 12.24.11 (4) [012W]: pagewise weak Serre membership propagates to every cohomology
object. -/
@[stacks 012W]
#check FilteredComplex.HasFiniteFiltrations.Cohomology.mem_of_page_mem

/- The explicit intermediate comparison used by both convergence and dévissage. -/
#check FilteredComplex.HasFiniteFiltrations.Convergence.isWeak
