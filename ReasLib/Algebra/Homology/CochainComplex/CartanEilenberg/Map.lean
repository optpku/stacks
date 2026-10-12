/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.AbutmentFunctor
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.AugmentationFunctor
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.DerivedPageFunctor
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.IsIso
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Additive

/-!
# Functorial API for Cartan--Eilenberg resolutions

This facade exports maps of Cartan--Eilenberg resolutions together with their row, column,
initial-page, total, filtered-total, and derived-abutment views.
-/

@[expose] public section
