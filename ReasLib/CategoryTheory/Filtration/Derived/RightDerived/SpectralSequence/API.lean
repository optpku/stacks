/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.API
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.API

/-!
# Right-derived spectral-sequence API

This is the neutral aggregate entry point for unbounded filtered right-derived spectral sequences.
The generic realization layer, the stupid-filtration specialization, and the truncation-filtration
specialization remain separate owners; this file only makes their public APIs available from one
stable import.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.FilteredComplex.RightDerived

end CategoryTheory.FilteredComplex.RightDerived
