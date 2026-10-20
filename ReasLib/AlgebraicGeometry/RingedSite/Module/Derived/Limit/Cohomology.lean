module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.Basis
public import ReasLib.CategoryTheory.Sites.EnoughObjects
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of basiswise-acyclic derived limits

This leaf owns the comparison between the cohomology sheaf of a sequential derived limit and the
ordinary inverse limit of the corresponding stage cohomology sheaves.  The local hypotheses are
the canonical `basiswiseAcyclic` and `basiswiseR1Vanishing` predicates, so the same bridge can be
used for any sequential tower of derived module objects.
-/

@[expose] public section

-- This is the standard quotient used by the named ringed-site models.
-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite.Hom.ModuleDerived.Limit
open scoped RingedSiteCohomology

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleDerived.Limit

variable (X : RingedSite.{u, v, w})
variable [UnivLE.{max u v, z}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)]

/-- Lemma 21.23.12 (0A09): basiswise acyclicity and vanishing of the section `R¹ lim` identify
the degree-`q` cohomology sheaf of a sequential derived limit with the ordinary inverse limit of
the degree-`q` cohomology sheaves of its stages. -/
@[stacks 0A09 "basiswise derived-limit cohomology comparison"]
theorem cohomologySheaf_iso_limit_of_basiswise_acyclic
    (Ksys : ℕᵒᵖ ⥤ ModuleDerived.{z} X)
    (K : ModuleDerived.{z} X)
    (hK : IsDerivedLimit Ksys K)
    (B : Set X)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (q : ℤ)
    (hacyclic :
      basiswiseAcyclic X B
        (Ksys ⋙ DerivedCategory.homologyFunctor (RingedSite.ModuleCat.{z} X) q))
    (hR1lim :
      basiswiseR1Vanishing X B
        (Ksys ⋙ DerivedCategory.homologyFunctor (RingedSite.ModuleCat.{z} X) q)) :
    IsIsomorphic
      (𝓗[q](X, K))
      (limit (Ksys ⋙ DerivedCategory.homologyFunctor (RingedSite.ModuleCat.{z} X) q)) := sorry

end RingedSite.Hom.ModuleDerived.Limit

end
