/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.SndFiber.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.SndFiber.FromFiber
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.SndFiber.Equivalence
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.SndFiber.Computations

/-!
# A costructured-arrow model for a second pseudo-pullback fibre

This aggregate exposes the costructured-arrow description of the fibre of the second
pseudo-pullback projection. The implementation is layered as follows:

* `Basic` owns the costructured-arrow category and forward comparison;
* `FromFiber` owns the inverse and its endpoint-transport formula;
* `Equivalence` owns explicit unit, counit, quasi-inverse, and equivalence data;
* `Computations` owns stable component formulas.

New developments should import the smallest leaf supplying the required API. The public surface
is organized under `BasedCategory.PseudoPullback.SndFiber`, with cospan-leg parameter order
`(F) (G)` matching `PseudoPullback F G`.
-/
