/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Compatibility.Targets
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Compatibility.Model
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Compatibility.Realization
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Compatibility.Map

/-!
# Finite Filtered Right-Derived Spectral-Sequence Compatibility

This aggregate retains the neutral `FilteredComplex.RightDerived.Finite` facade without
introducing wrapper declarations.  Import the `Targets`, `Model`, `Realization`, or `Map` leaf
directly when only one layer is needed.
-/
