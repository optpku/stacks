/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Comparison
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PositivePage.API
public import ReasLib.CategoryTheory.Homology.SpectralSequence.FromPage
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.API
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Bounded.FromZero
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageFiltration
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageFiltration.Naturality
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageFiltration.Preadditive
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageFiltration.IsIso
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageOneRow
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageOneRow.Preadditive
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageOneRow.IsIso
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageZeroColumn
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageZeroColumn.Preadditive
public import ReasLib.CategoryTheory.Homology.SpectralSequence.PageZeroColumn.IsIso
public import ReasLib.CategoryTheory.Homology.SpectralSequence.ChangeOfCategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Public API for spectral-sequence infrastructure

This is the neutral downstream entry point for the reusable spectral-sequence layer.  It gathers
the page-one and renumbering APIs, page filtrations, fixed rows and columns, boundedness from a
zero-based sequence, and change of target category.  The owner files remain available for clients
that need a smaller import boundary.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.SpectralSequence

end CategoryTheory.SpectralSequence

namespace CategoryTheory.CohomologicalSpectralSequence

end CategoryTheory.CohomologicalSpectralSequence
