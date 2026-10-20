/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Targets

/-!
# Short Names for Finite Filtered Right-Derived Targets

This export-only leaf exposes the complex, pointwise value, page-one, and abutment targets under
the neutral `FilteredComplex.RightDerived.Finite` namespace.
-/

@[expose] public section

namespace CategoryTheory.FilteredComplex.RightDerived.Finite

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
  (gradedPieceComplex underlyingComplex gradedPieceComplexMap underlyingComplexMap
    gradedPieceSource underlyingSource gradedPieceSourceMap underlyingSourceMap gradedPiece
    underlying gradedPieceMap underlyingMap gradedPieceMap_id gradedPieceMap_comp underlyingMap_id
    underlyingMap_comp)

namespace GradedPiece

export CategoryTheory.FilteredObject.Finite.Plus.GradedPiece (cochain homotopy)

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.GradedPiece
  (functor functor_obj functor_map)

end GradedPiece

namespace Underlying

export CategoryTheory.FilteredObject.Finite.Plus.Forget (cochain homotopy)

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Underlying
  (functor functor_obj functor_map)

end Underlying

namespace PageOne

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.PageOne
  (functor obj map functor_obj functor_map)

end PageOne

namespace Abutment

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Abutment
  (functor obj map functor_obj functor_map)

end Abutment

end CategoryTheory.FilteredComplex.RightDerived.Finite
