/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Model.Comparison.Total

/-!
# Short Names for Finite Filtered Right-Derived Models

This export-only leaf exposes model construction and comparison under the neutral
`FilteredComplex.RightDerived.Finite.Model` namespace.
-/

@[expose] public section

namespace CategoryTheory.FilteredComplex.RightDerived.Finite

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
  (modelFunctor model modelMap modelMap_id modelMap_comp modelMap_reindex)

namespace Model

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model
  (Comparison functor functor_obj functor_map)

namespace GradedPiece

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model.GradedPiece
  (cochainIso derivedIso homologyIso homologyIso_hom homologyIso_inv
    cochainIso_hom_naturality cochainIso_inv_naturality derivedIso_hom_naturality
    derivedIso_inv_naturality homologyIso_hom_naturality homologyIso_inv_naturality
    cochainIso_source_map cochainIso_target_map derivedIso_source_map derivedIso_target_map
    homologyIso_source_map homologyIso_target_map)

namespace Homology

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model.GradedPiece.Homology
  (source target source_obj source_map target_obj target_map homologyIso_naturality natIso
    natIso_hom_app natIso_inv_app natIso_hom_naturality natIso_inv_naturality)

end Homology

end GradedPiece

namespace Underlying

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model.Underlying
  (derivedIso homologyIso homologyIso_hom homologyIso_inv derivedIso_hom_naturality
    derivedIso_inv_naturality homologyIso_hom_naturality homologyIso_inv_naturality
    derivedIso_source_map derivedIso_target_map homologyIso_source_map homologyIso_target_map)

namespace Homology

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model.Underlying.Homology
  (source target source_obj source_map target_obj target_map homologyIso_naturality natIso
    natIso_hom_app natIso_inv_app natIso_hom_naturality natIso_inv_naturality)

end Homology

end Underlying

namespace Comparison

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model.Comparison
  (gradedPieceIso underlyingIso nonempty IsCompatible ofResolution ofResolution_gradedPieceIso
    ofResolution_underlyingIso)

namespace IsCompatible

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Model.Comparison.IsCompatible
  (gradedPieceSq underlyingSq id comp reindex gradedPiece_naturality gradedPiece_inv_naturality
    underlying_naturality underlying_inv_naturality gradedPiece_naturality_inv
    underlying_naturality_inv ofResolution)

end IsCompatible

end Comparison

end Model

end CategoryTheory.FilteredComplex.RightDerived.Finite
