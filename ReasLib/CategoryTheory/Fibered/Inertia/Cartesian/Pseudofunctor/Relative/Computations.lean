/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Computations.Action
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Computations.TwoCell
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Computations.Comparisons

/-!
# Computations for the fibred relative-inertia pseudofunctor

This is the stable aggregate for the relative-inertia computation facade.
`Computations.Action` identifies the packaged action with its explicit owners;
`Computations.TwoCell` exposes total-category components and naturality;
`Computations.Comparisons` owns both directions of identity and composition
comparisons down to objectwise components.
-/
