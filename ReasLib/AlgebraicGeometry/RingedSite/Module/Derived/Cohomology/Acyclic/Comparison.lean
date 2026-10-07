module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology.Acyclic.Limit
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying.Cohomology
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Degeneration
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hypercohomology from acyclic cohomology sheaves

This final leaf combines the objectwise acyclicity predicates with the lower-truncation limit
criterion and the reusable single-column degeneration theorem.  Keeping those imports here makes
the convergence input for an unbounded derived module visible without burdening predicate-only
consumers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped RingedSiteCohomology

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleDerived.CohomologySheaves

variable (X : RingedSite.{u, v, w})
variable [UnivLE.{max u v, z}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)]

/-- Lemma 21.23.11 (0BKZ): on a covering family of objects over which all cohomology sheaves
are acyclic, hypercohomology is concentrated in the degree-zero cohomology of the corresponding
cohomology sheaf. -/
@[stacks 0BKZ "cohomology from acyclic cohomology sheaves"]
theorem cohomologyOverObject_isomorphic_zeroDegree
    (K : RingedSite.Hom.ModuleDerived.{z} X) (B : Set X)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hacyclic : IsAcyclicOn X B K) {U : X} (hU : U ∈ B) (q : ℤ) :
    IsIsomorphic
      (RingedSite.Hom.ModuleDerived.cohomologyOverObject.{z} X U K q)
      (RingedSite.Hom.ModuleDerived.cohomologyOverObject.{z} X U (asDerived X K q) 0) := sorry

end RingedSite.Hom.ModuleDerived.CohomologySheaves

end
