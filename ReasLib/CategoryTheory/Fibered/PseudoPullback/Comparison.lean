/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Comparison.Functor
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Comparison.Equivalence

/-!
# Comparing fibred and categorical pseudo-pullbacks

This compatibility import exposes both layers of the comparison API:

* `Comparison.Functor` owns the deterministic functor to mathlib's categorical pullback and its
  object, map, and base-projection computations;
* `Comparison.Equivalence` owns the fibredness-dependent equivalence choices and their inverse
  base-projection compatibility.

New developments should import the smaller leaf matching their need. This aggregate remains the
stable compatibility entry point for existing downstream applications. The preferred role-based
surface is `BasedCategory.PseudoPullback.Comparison.functor` for deterministic object/map and
projection computations, `Comparison.{fstBaseIso,sndBaseIso}` for base compatibility, and
`Comparison.{equivalence,equivalenceOfLeft}` for the two fibredness-dependent equivalence
choices.
-/
