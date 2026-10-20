/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Objects.Computations
public import ReasLib.CategoryTheory.Fibered.Inertia.Based.Computations

/-!
# Fibred inertia objects

Compatibility aggregate for the bundled relative and absolute inertia owners
and their projection/total-category computations. It also re-exports the
neutral forgetful-map computations needed to interpret these bundled objects
on total categories. Import the focused leaves directly when only one layer is
needed.
-/
