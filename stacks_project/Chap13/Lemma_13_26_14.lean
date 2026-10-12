/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Compatibility
import ReasLib.CategoryTheory.Filtration.Complex.SpectralSequenceComparison
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.26.14

The reusable owner works directly with bounded-below complexes of finite filtered objects. This
keeps boundedness and finiteness in the source type and leaves only enough injectives as the
source-side existence hypothesis.
-/

namespace CategoryTheory.FilteredComplex.RightDerived.Finite

/- Lemma 13.26.14 (`015W`): the filtered right-derived spectral sequence. -/
@[stacks 015W] #check @existsSpectralSequence
#check @CochainComplex.FilteredInjectivePlus.Resolution
#check @CochainComplex.FilteredInjectivePlus.Resolution.Map
#check @gradedPieceComplex
#check @underlyingComplex
#check @gradedPieceComplexMap
#check @underlyingComplexMap
#check @PageOne.functor
#check @PageOne.functor_obj
#check @PageOne.functor_map
#check @Abutment.functor
#check @Abutment.functor_obj
#check @Abutment.functor_map
#check @model
#check @modelMap
#check @Model.Comparison
#check @Model.functor
#check @Model.functor_obj
#check @Model.functor_map
#check @Model.Comparison.nonempty
#check @Model.GradedPiece.cochainIso
#check @Model.GradedPiece.derivedIso
#check @Model.GradedPiece.homologyIso
#check @Model.GradedPiece.homologyIso_hom
#check @Model.GradedPiece.homologyIso_inv
#check @Model.GradedPiece.cochainIso_hom_naturality
#check @Model.GradedPiece.cochainIso_inv_naturality
#check @Model.GradedPiece.derivedIso_hom_naturality
#check @Model.GradedPiece.derivedIso_inv_naturality
#check @Model.GradedPiece.homologyIso_hom_naturality
#check @Model.GradedPiece.homologyIso_inv_naturality
#check @Model.GradedPiece.Homology.natIso
#check @Model.GradedPiece.Homology.natIso_hom_app
#check @Model.GradedPiece.Homology.natIso_inv_app
#check @Model.GradedPiece.Homology.natIso_hom_naturality
#check @Model.GradedPiece.Homology.natIso_inv_naturality
#check @Model.Underlying.derivedIso
#check @Model.Underlying.homologyIso
#check @Model.Underlying.homologyIso_hom
#check @Model.Underlying.homologyIso_inv
#check @Model.Underlying.derivedIso_hom_naturality
#check @Model.Underlying.derivedIso_inv_naturality
#check @Model.Underlying.homologyIso_hom_naturality
#check @Model.Underlying.homologyIso_inv_naturality
#check @Model.Underlying.Homology.natIso
#check @Model.Underlying.Homology.natIso_hom_app
#check @Model.Underlying.Homology.natIso_inv_app
#check @Model.Underlying.Homology.natIso_hom_naturality
#check @Model.Underlying.Homology.natIso_inv_naturality
#check @Model.Comparison.ofResolution
#check @Model.Comparison.ofResolution_gradedPieceIso
#check @Model.Comparison.ofResolution_underlyingIso
#check @Model.Comparison.IsCompatible
#check @Model.Comparison.IsCompatible.ofResolution
#check @Model.Comparison.IsCompatible.id
#check @Model.Comparison.IsCompatible.comp
#check @Model.Comparison.IsCompatible.reindex
#check @Model.Comparison.IsCompatible.gradedPiece_naturality_inv
#check @Model.Comparison.IsCompatible.underlying_naturality_inv
#check @Realization
#check @Realization.ofResolution
#check @Realization.ofResolution_resolution
#check @Realization.ofResolution_comparison
#check @Realization.ofResolution_associated
#check @Realization.ofResolution_pageOneIso
#check @Realization.ofResolution_targetIso
#check @Realization.nonemptyOfResolution
#check @Realization.comparison
#check @Realization.pageOneIso_hom
#check @Realization.pageOneIso_inv
#check @Realization.Map
#check @Realization.Map.comparisonCompatible
#check @Realization.Map.ofResolutionMap
#check @Realization.Map.nonemptyOfResolutionMap
#check @Realization.Map.ofResolution
#check @Realization.Map.ofResolution_resolutionMap
#check @Realization.Map.ofResolution_associationMap
#check @Realization.Map.ofResolution_filteredMap
#check @Realization.Map.ofResolution_sequenceMap
#check @Realization.Map.nonemptyOfResolution
#check @Realization.Map.ext
#check @Realization.Map.pageOne_hom
#check @Realization.Map.target_hom
#check @Realization.Map.id
#check @Realization.Map.id_resolutionMap
#check @Realization.Map.id_filteredMap
#check @Realization.Map.id_sequenceMap
#check @Realization.Map.comp
#check @Realization.Map.comp_resolutionMap
#check @Realization.Map.comp_filteredMap
#check @Realization.Map.comp_sequenceMap
#check @Realization.Map.reindex
#check @Realization.Map.reindex_resolutionMap
#check @Realization.Map.reindex_filteredMap
#check @Realization.Map.reindex_sequenceMap
#check @Realization.Map.reindex_rfl
#check @Realization.toWithAbutment
#check @Realization.toWithAbutment_toRealization
#check @Realization.toWithAbutment_abutmentIso
#check @Realization.Map.toWithAbutmentMap
#check @Realization.Map.toWithAbutmentMap.id
#check @Realization.Map.toWithAbutmentMap.comp
#check @Realization.Map.toWithAbutmentMap.reindex
#check @Realization.Map.id_comp
#check @Realization.Map.comp_id
#check @Realization.Map.assoc
#check @FilteredComplex.SpectralSequence.Realization.Map
#check @FilteredComplex.SpectralSequence.Realization.Map.id
#check @FilteredComplex.SpectralSequence.Realization.Map.id_filteredMap
#check @FilteredComplex.SpectralSequence.Realization.Map.id_sequenceMap
#check @FilteredComplex.SpectralSequence.Realization.Map.comp
#check @FilteredComplex.SpectralSequence.Realization.Map.comp_filteredMap
#check @FilteredComplex.SpectralSequence.Realization.Map.comp_sequenceMap

/- Functorial conversion to the neutral realization-with-abutment layer. -/
#check @Realization.Total
#check @Realization.Total.forgetBase
#check @Realization.Total.forgetBase_obj
#check @Realization.Total.forgetBase_map
#check @Realization.displayedFunctor
#check @Realization.displayedFunctor_obj
#check @Realization.displayedFunctor_map
#check @Realization.resolutionDisplayedFunctor
#check @Realization.resolutionDisplayedFunctor_obj
#check @Realization.resolutionDisplayedFunctor_map
#check @Realization.resolutionFunctor
#check @Realization.resolutionFunctor_forgetBase
#check @Realization.resolutionFunctor_obj_obj
#check @Realization.resolutionFunctor_map_displayed
#check @Realization.withAbutmentFunctor
#check @Realization.withAbutmentFunctor_forgetBase
#check @Realization.withAbutmentFunctor_obj_obj
#check @Realization.withAbutmentFunctor_map_displayed
#check @FilteredComplex.SpectralSequence.Realization.WithAbutment.abutmentComparison
#check @Realization.pageOneSource
#check @Realization.pageOneSource_map
#check @Realization.pageOneTarget
#check @Realization.pageOneTarget_map
#check @Realization.pageOneComparison
#check @Realization.pageOneComparison_app
#check @Realization.pageOneComparison_hom_app
#check @Realization.pageOneComparison_inv_app
#check @Realization.pageOneComparison_source_map
#check @Realization.pageOneComparison_target_map
#check @Realization.pageOneComparison_hom_naturality
#check @Realization.pageOneComparison_inv_naturality
#check @Realization.abutmentSource
#check @Realization.abutmentSource_map
#check @Realization.abutmentTarget
#check @Realization.abutmentTarget_map
#check @Realization.abutmentComparison
#check @Realization.abutmentComparison_app
#check @Realization.abutmentComparison_hom_app
#check @Realization.abutmentComparison_inv_app
#check @Realization.abutmentComparison_source_map
#check @Realization.abutmentComparison_target_map
#check @Realization.abutmentComparison_hom_naturality
#check @Realization.abutmentComparison_inv_naturality

/- Functoriality in the bounded-below finite filtered complex. -/
#check @existsMap
#check @gradedPieceMap_id
#check @gradedPieceMap_comp
#check @underlyingMap_id
#check @underlyingMap_comp

/- Independence of choices from the first page onward. -/
#check @Realization.existsIsoFromOne
#check @CategoryTheory.FilteredComplex.Association.Hom.isIsoFrom
#check @CategoryTheory.FilteredComplex.Association.Hom.existsIso

end CategoryTheory.FilteredComplex.RightDerived.Finite
