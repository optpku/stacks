/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.Computation
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.Preadditive
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.IsIso
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.FromZero.Comparison
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.FromZero.Preadditive
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.FromZero.IsIso
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Renumber.FromZero.Relation

/-!
# Public API for cohomological spectral-sequence renumbering

This facade exports the generic `E₁`-to-`E₂` renumbering and the standard composite from a
zero-based sequence, including computation, comparison, relation, additivity, and `IsIso` APIs.
-/

@[expose] public section

namespace CategoryTheory.CohomologicalSpectralSequence.Renumber

end CategoryTheory.CohomologicalSpectralSequence.Renumber
