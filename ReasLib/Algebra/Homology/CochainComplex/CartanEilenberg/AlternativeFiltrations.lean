/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.AlternativeFiltrations.Realization
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.AlternativeFiltrations.First
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.AlternativeFiltrations.Second

/-!
# Alternative Filtrations for Cartan--Eilenberg Spectral Sequences

This facade exports the independently owned realization, first-page, and second-page comparison
APIs for the stupid and canonical-truncation filtrations.
-/

@[expose] public section

open CategoryTheory
