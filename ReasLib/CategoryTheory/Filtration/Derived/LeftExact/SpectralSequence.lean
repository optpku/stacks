/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Existence
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Compatibility

/-!
# Finite filtered right-derived spectral sequences

This facade reexports the pointwise targets, strict filtered model, comparison data, realization
objects, realization maps and their category laws, and the source-faithful existence statements.
Downstream developments should import a leaf when they need only one layer.
-/

@[expose] public section
