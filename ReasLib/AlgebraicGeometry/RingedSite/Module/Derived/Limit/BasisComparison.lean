/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Limit.Basis
public import ReasLib.CategoryTheory.Sites.EnoughObjects
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

-- This is the standard quotient used by the named ringed-site models.
-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard

/-!
# Basiswise comparisons for derived limits

This leaf owns the ringed-site specialization of the sequential derived-limit comparison under
basiswise acyclicity.  The hypotheses use the reusable predicates from `Limit.Basis`; the chapter
presentation is consequently only a recall of these two atomic conclusions.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped RingedSiteCohomology

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleDerived.Limit

variable (X : RingedSite.{u, v, w})
variable [UnivLE.{max u v, z}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)]

namespace Single

/-- Lemma 21.23.5 (0BKY) (1): if `B` is a cohomology basis, the chosen derived limit of a
degree-zero tower is isomorphic to the degree-zero single object on its ordinary inverse limit. -/
@[stacks 0BKY "derived limit equals the ordinary limit on a cohomology basis"]
theorem iso_limit_of_basiswise
    (B : Set X)
    (F : ℕᵒᵖ ⥤ RingedSite.ModuleCat.{z} X)
    (K : ModuleDerived.{z} X)
    (hK : IsDerivedLimit
      (F ⋙ DerivedCategory.singleFunctor (RingedSite.ModuleCat.{z} X) (0 : ℤ)) K)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hacyclic : basiswiseAcyclic X B F)
    (hR1lim : basiswiseR1Vanishing X B F) :
    IsIsomorphic
      K
      ((DerivedCategory.singleFunctor (RingedSite.ModuleCat.{z} X) (0 : ℤ)).obj
        (limit F)) := sorry

/-- Lemma 21.23.5 (0BKY) (2): the ordinary inverse limit has vanishing positive cohomology on
every object of the basis. -/
@[stacks 0BKY "higher cohomology of the ordinary inverse limit vanishes on the basis"]
theorem limit_cohomology_isZero_of_basiswise
    (B : Set X)
    (F : ℕᵒᵖ ⥤ RingedSite.ModuleCat.{z} X)
    (K : ModuleDerived.{z} X)
    (hK : IsDerivedLimit
      (F ⋙ DerivedCategory.singleFunctor (RingedSite.ModuleCat.{z} X) (0 : ℤ)) K)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hacyclic : basiswiseAcyclic X B F)
    (hR1lim : basiswiseR1Vanishing X B F)
    (U : X) (hU : U ∈ B) (p : ℤ) (hp : 0 < p) :
    IsZero
      (RingedSite.Hom.ModuleDerived.cohomologyOverObject.{z} X U
        ((DerivedCategory.singleFunctor (RingedSite.ModuleCat.{z} X) (0 : ℤ)).obj
          (limit F)) p) := sorry

end Single

end RingedSite.Hom.ModuleDerived.Limit

end
