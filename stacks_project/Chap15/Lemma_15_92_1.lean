module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Criteria
public import ReasLib.RingTheory.Algebra.IsEpi.Localization
import ReasLib.RingTheory.Algebra.IsEpi.ModuleCat
import ReasLib.RingTheory.Algebra.IsEpi.TensorSquare
import StacksCheckRecall

/-!
# Lemma 15.92.1: equivalent criteria for derived localization vanishing

@stack 091P

The reusable localization-away tower, selected internal-Hom object, and atomic vanishing criteria
are owned by `ReasLib.Algebra.Homology.DerivedCategory.Completeness`.  This chapter file retains
only the source-facing ring-epimorphism and owner checks.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory

export _root_.DerivedCategory
  (localizationAwayDerivedHomVanishingCondition IsDerivedCompleteWithRespectTo
    isDerivedCompleteWithRespectTo_iff derivedCompleteObjectProperty)

/- Lemma 15.92.1 (Stacks `091P`): the localization map `A → A_f` is an epimorphism of
commutative rings.  The reusable instance is owned by `ReasLib.RingTheory.Algebra.IsEpi.Localization`.
-/
@[stacks 091P "localization-away ring epimorphism"]
#check @RingHom.localizationAway_epi

end CategoryTheory.DerivedCategory

/- The source-facing chapter checks the shared owners without defining a second implementation. -/
namespace CategoryTheory.DerivedCategory
@[stacks 091P "shared localization-away tower"]
#check @localizationAwayTower
@[stacks 091P "shared localization-away internal Hom"]
#check @localizationAwayT
@[stacks 091P "shared localization-away derived-limit predicate"]
#check @localizationAwayT_isHomotopyLimit
@[stacks 091P "shared localization-away vanishing criterion"]
#check @localizationAwayT_isZero_iff
@[stacks 091P "shared localization-away predicate bridge"]
#check @localizationAwayDerivedHomVanishingCondition_iff
end CategoryTheory.DerivedCategory

namespace ModuleCat
@[stacks 091P "shared module localization-away predicate"]
#check @moduleLocalizationAwayTVanishing
@[stacks 091P "shared module localization-away bridge"]
#check @moduleLocalizationAwayTVanishing_iff
end ModuleCat

namespace CategoryTheory.DerivedCategory.LocalizationAway
@[stacks 091P "all-degree localization-away Ext criterion"]
#check @extVanishing
@[stacks 091P "all-source localization-away derived-Hom criterion"]
#check @_root_.DerivedCategory.localizationAwayDerivedHomVanishingCondition
@[stacks 091P "cohomologywise localization-away T criterion"]
#check @cohomologyTVanishing
@[stacks 091P "cohomologywise localization-away low-Ext criterion"]
#check @cohomologyLowExtVanishing
@[stacks 091P "explicit localization-away tower product cone"]
#check @ProductCone
@[stacks 091P "explicit localization-away product difference"]
#check @productDifference
@[stacks 091P "localization-away product-difference criterion for a chosen product cone"]
#check @productDifferenceIsIsoAt
@[stacks 091P "localization-away product-difference isomorphism criterion"]
#check @productDifferenceIsIso
@[stacks 091P "localization-away product-difference component formula"]
#check @productDifference_comp_projection
@[stacks 091P "all-degree Ext and all-source derived-Hom equivalence"]
#check @extVanishing_iff_derivedHomVanishing
@[stacks 091P "T and cohomologywise T vanishing equivalence"]
#check @t_isZero_iff_cohomologyTVanishing
@[stacks 091P "cohomologywise T and low-Ext equivalence"]
#check @cohomologyTVanishing_iff_lowExtVanishing
@[stacks 091P "T and derived internal-Hom vanishing equivalence"]
#check @t_isZero_iff_rhom_isZero
@[stacks 091P "T and explicit product-difference equivalence"]
#check @t_isZero_iff_productDifference_isIso
@[stacks 091P "T and product-independent difference equivalence"]
#check @t_isZero_iff_productDifferenceIsIso
end CategoryTheory.DerivedCategory.LocalizationAway
