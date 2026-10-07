module

public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact.SpectralSequence.Compatibility.Realization

/-!
# Short Names for Finite Filtered Right-Derived Realization Maps

This export-only leaf exposes map construction, computation, naturality, reindexing, and
isomorphism transport under `FilteredComplex.RightDerived.Finite.Realization.Map`.
-/

@[expose] public section

namespace CategoryTheory.FilteredComplex.RightDerived.Finite.Realization.Map

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization.Map
  (resolutionMap comparisonCompatible associationMap ofResolutionMap nonemptyOfResolutionMap
    ofResolution ofResolution_resolutionMap ofResolution_associationMap ofResolution_filteredMap
    ofResolution_sequenceMap nonemptyOfResolution pageOneSq targetSq filteredMap sequenceMap ext
    pageOne_hom pageOne_hom_assoc target_hom target_hom_assoc pageOne_inv_naturality
    pageOne_inv_naturality_assoc target_inv_naturality target_inv_naturality_assoc
    pageOne_naturality_inv pageOne_naturality_inv_assoc pageOne_target_map
    pageOne_target_map_assoc target_naturality_inv target_naturality_inv_assoc target_map
    target_map_assoc idAssociationCompatible idAssociationMap idPageOne idTarget id
    id_resolutionMap id_filteredMap id_sequenceMap id_associationMap compAssociationCompatible
    compAssociationMap compPageOne compTarget comp comp_resolutionMap comp_filteredMap
    comp_sequenceMap comp_associationMap reindexAssociationCompatible reindexAssociationMap
    reindexPageOne reindexTarget reindex reindex_resolutionMap reindex_filteredMap
    reindex_sequenceMap reindex_associationMap reindex_rfl reindex_eq_cast cast_eq_reindex
    toWithAbutmentMap toFilteredMap id_comp comp_id assoc isIsoFrom isIsoFromOne
    sequenceMap_isIso sequenceMap_f_isIso pageOneMap_isIso_of_filteredMap
    abutmentMap_isIso_of_filteredMap)

namespace toWithAbutmentMap

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization.Map.toWithAbutmentMap
  (toRealizationMap filteredMap sequenceMap toAssociationHom id comp reindex)

end toWithAbutmentMap

namespace toFilteredMap

export CategoryTheory.FilteredObject.Finite.RightDerived.SpectralSequence.Realization.Map.toFilteredMap
  (filteredMap sequenceMap association_hom toAssociationHom eq_of_filteredMap_eq id comp reindex)

end toFilteredMap

end CategoryTheory.FilteredComplex.RightDerived.Finite.Realization.Map
