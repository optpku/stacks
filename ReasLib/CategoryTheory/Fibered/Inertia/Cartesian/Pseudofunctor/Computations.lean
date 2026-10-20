/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Computations.Action
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Computations.TwoCell
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Computations.Comparisons

/-!
# Computations for the fibred-inertia pseudofunctor

This is the stable aggregate for the ordinary fibred-inertia computation
facade.  `Computations.Action` owns object and owner identifications;
`Computations.TwoCell` owns total-category `2`-cell projections;
`Computations.Comparisons` owns both directions of identity and composition
comparisons down to components.
-/
