/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration.InitialPages.First
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration.InitialPages.Second

/-!
# Initial Pages of the Standard Double-Complex Filtrations

Compatibility aggregate for the initial-page APIs of the two standard filtrations.  New clients
may import `InitialPages.First` or `InitialPages.Second` directly when only one filtration is
needed; graded-piece homology is available separately from `Filtration.GradedPieceHomology`.
-/
