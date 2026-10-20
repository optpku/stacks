/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.HomotopyCategory.TotalFunctor

/-!
# Lemma 15.58.2

@stack 064I

The homotopy calculation is already the generic
`HomologicalComplex.mapBifunctorMapHomotopy₁` API.  Its descent to the
homotopy category is the named `rightFixed` functor, so the chapter entry
does not duplicate either construction.
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.58.2: tensoring a homotopy in the varying left factor with a fixed
right factor gives a homotopy after totalization. -/
@[stacks 064I "totalized tensor preserves homotopies"]
#check @HomologicalComplex.mapBifunctorMapHomotopy₁

/- The induced endofunctor on the homotopy category is the reusable fixed-right owner. -/
@[stacks 064I "fixed-right totalization on the homotopy category"]
#check @Functor.Homotopy.BifunctorTotal.rightFixed

#check @Functor.Homotopy.BifunctorTotal.rightPreservesHomotopy
