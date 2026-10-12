/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.Displayed
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Existence
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Realization.Resolution
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Total.Abutment
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Total.PageOne

/-!
# Short Names for Finite Filtered Right-Derived Realizations

This export-only leaf exposes realization objects, displayed and total functors, page-one and
abutment comparisons, and existence interfaces under the neutral
`FilteredComplex.RightDerived.Finite.Realization` namespace.  Map computations live in the
separate `Compatibility.Map` leaf.
-/

@[expose] public section

namespace CategoryTheory.FilteredComplex.RightDerived.Finite

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence
  (Realization existsSpectralSequence existsMap displayedCategory displayedCategory_obj
    displayedCategory_hom displayedCategory_id displayedCategory_comp)

namespace Realization

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization
  (Total resolution comparison associated pageOneIso pageOneIso_hom pageOneIso_inv targetIso
    filtered sequence association isAssociated isBounded ofResolution ofResolution_resolution
    ofResolution_comparison ofResolution_associated ofResolution_filtered ofResolution_sequence
    ofResolution_association ofResolution_pageOneIso ofResolution_targetIso nonemptyOfResolution
    finite converges toFilteredRealization toFilteredRealization_filtered
    toFilteredRealization_sequence toFilteredRealization_association
    toFilteredRealization_bounded toFilteredRealization_finite toFilteredRealization_converges
    toWithAbutment toWithAbutment_toRealization toWithAbutment_abutmentIso
    displayedFunctor displayedFunctor_obj displayedFunctor_map withAbutmentFunctor
    withAbutmentFunctor_forgetBase withAbutmentFunctor_obj_base withAbutmentFunctor_obj_obj
    withAbutmentFunctor_map_base withAbutmentFunctor_map_displayed abutmentSource
    abutmentSource_obj abutmentSource_map abutmentTarget abutmentTarget_obj abutmentTarget_map
    abutmentComparison abutmentComparison_app abutmentComparison_hom_app
    abutmentComparison_inv_app abutmentComparison_source_map abutmentComparison_target_map
    abutmentComparison_hom_naturality abutmentComparison_inv_naturality pageOneSource
    pageOneSource_obj pageOneSource_map pageOneTarget pageOneTarget_obj pageOneTarget_map
    pageOneComparison pageOneComparison_app pageOneComparison_hom_app pageOneComparison_inv_app
    pageOneComparison_source_map pageOneComparison_target_map pageOneComparison_hom_naturality
    pageOneComparison_inv_naturality resolutionDisplayedFunctor resolutionDisplayedFunctor_obj
    resolutionDisplayedFunctor_map resolutionDisplayedFunctor_map_id
    resolutionDisplayedFunctor_map_comp resolutionFunctor resolutionFunctor_forgetBase
    resolutionFunctor_obj_base resolutionFunctor_obj_obj resolutionFunctor_map_base
    resolutionFunctor_map_displayed functor functor_obj functor_map functor_map_id
    functor_map_comp Map existsIsoFromOne)

namespace Total

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization.Total
  (forgetBase forgetBase_obj forgetBase_map)

end Total

end Realization

end CategoryTheory.FilteredComplex.RightDerived.Finite
