/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying.Limit
public import ReasLib.CategoryTheory.Sites.Family.Cofinal
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cofinal-cover comparison for sequential derived limits

The stage comparison is stated using the canonical `IsDerivedLimit.stageProjection` and the
set-valued cofinal-cover predicate.  This removes presentation-specific equality witnesses while
retaining the source's sectionwise injectivity conclusion.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology
open RingedSite.Hom.ModuleSections.Underlying

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleDerived.Limit

variable (X : RingedSite.{u, v, w})
variable [UnivLE.{max u v, z}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)]

/-- Lemma 21.23.6 (0D6L): cofinal local vanishing and eventual injectivity make the canonical
stage projection injective on degree-`m` cohomology sections. -/
@[stacks 0D6L "cofinal-cover stage comparison"]
theorem stageProjection_mono_of_cofinal
    (Ksys : SequentialInverseSystem (RingedSite.Hom.ModuleDerived.{z} X))
    (K : RingedSite.Hom.ModuleDerived.{z} X)
    (V : X) (m : ℤ) (nV : ℕ)
    (hK : IsDerivedLimit Ksys K)
    (CovV : Set (X.siteTopology.Cover V))
    (hcofinal : cofinalCoverFamily X.siteTopology V CovV)
    (hR1vanish :
      ∀ ⦃T : X.siteTopology.Cover V⦄, T ∈ CovV → ∀ I : T.Arrow,
        IsZero ((cohomologyTower X I.Y Ksys (m - 1)).firstDerivedLimit))
    (hinj :
      ∀ ⦃T : X.siteTopology.Cover V⦄, T ∈ CovV → ∀ I : T.Arrow, ∀ n : ℕ, ∀ hn : nV ≤ n,
        Mono ((cohomologyTower X I.Y Ksys m).transitionMap hn)) :
    Mono
      ((RingedSite.Hom.ModuleDerived.cohomologySheafMap X m (hK.stageProjection nV)).1.app
        (op V)) := sorry

end RingedSite.Hom.ModuleDerived.Limit

end
