/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.LowerResolution.Injective.Derived
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Comparison
public import ReasLib.CategoryTheory.Sites.EnoughObjects
public import ReasLib.CategoryTheory.Sites.Family.Cofinal
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Basiswise truncation-limit hypotheses

This leaf owns the local vanishing predicates used in truncation-limit arguments.  The predicates
are separated from the comparison theorem so that a later argument can reuse the same basiswise
conditions with a different derived-limit construction.
-/

open CategoryTheory CategoryTheory.Limits Opposite
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
open scoped RingedSiteCohomology

noncomputable section

universe z u v w

namespace RingedSite.Hom.ModuleDerived.Limit

variable (X : RingedSite.{u, v, w})
variable [UnivLE.{max u v, z}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{z} X)]

namespace Basis

/-- Eventual local vanishing over `V`, with a cofinal family of covers and a degree bound. -/
@[stacks 0D6M "basiswise eventual cohomology vanishing"]
def eventual (E : ModuleDerived.{z} X) (V : X) : Prop :=
  ∃ (pBound : ℤ → ℤ) (CovV : Set (X.siteTopology.Cover V)),
    CategoryTheory.GrothendieckTopology.cofinalCoverFamily
        X.siteTopology V CovV ∧
      ∀ ⦃T : X.siteTopology.Cover V⦄, T ∈ CovV → ∀ I : T.Arrow, ∀ p m : ℤ,
        pBound m < p →
          IsZero
            (RingedSite.Hom.ModuleDerived.cohomologyOverObject.{z} X I.Y
              ((DerivedCategory.singleFunctor (RingedSite.ModuleCat.{z} X) (0 : ℤ)).obj
                (RingedSite.Hom.ModuleDerived.cohomologySheaf.{z} X E (m - p))) p)

/-- Negative-degree local vanishing over `V`, with a natural-number cohomological bound. -/
@[stacks 0D6N "basiswise negative cohomology vanishing"]
def negative (E : ModuleDerived.{z} X) (V : X) : Prop :=
  ∃ (dV : ℕ) (CovV : Set (X.siteTopology.Cover V)),
    CategoryTheory.GrothendieckTopology.cofinalCoverFamily
        X.siteTopology V CovV ∧
      ∀ ⦃T : X.siteTopology.Cover V⦄, T ∈ CovV → ∀ I : T.Arrow, ∀ p q : ℤ,
        (dV : ℤ) < p → q < 0 →
          IsZero
            (RingedSite.Hom.ModuleDerived.cohomologyOverObject.{z} X I.Y
              ((DerivedCategory.singleFunctor (RingedSite.ModuleCat.{z} X) (0 : ℤ)).obj
                (RingedSite.Hom.ModuleDerived.cohomologySheaf.{z} X E q)) p)

/-- Uniform negative-degree vanishing on a subset `B`, with one bound shared by the subset. -/
@[stacks 0D6P "uniform basiswise negative cohomology vanishing"]
def uniformNegative (E : ModuleDerived.{z} X) (d : ℕ) (B : Set X) : Prop :=
  ∀ ⦃V : X⦄, V ∈ B → ∀ p q : ℤ, (d : ℤ) < p → q < 0 →
    IsZero
      (RingedSite.Hom.ModuleDerived.cohomologyOverObject.{z} X V
        ((DerivedCategory.singleFunctor (RingedSite.ModuleCat.{z} X) (0 : ℤ)).obj
          (RingedSite.Hom.ModuleDerived.cohomologySheaf.{z} X E q)) p)

/-- A uniform eventual bound produces the per-object eventual owner. -/
@[stacks 08U3 "uniform basiswise eventual bridge"]
theorem eventual.of_uniform
    {E : ModuleDerived.{z} X} (pBound : ℤ → ℤ) (B : Set X)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hvanish :
      ∀ ⦃V : X⦄, V ∈ B → ∀ p m : ℤ, pBound m < p →
        IsZero
          (RingedSite.Hom.ModuleDerived.cohomologyOverObject.{z} X V
            ((DerivedCategory.singleFunctor (RingedSite.ModuleCat.{z} X) (0 : ℤ)).obj
              (RingedSite.Hom.ModuleDerived.cohomologySheaf.{z} X E (m - p))) p))
    (V : X) :
    eventual X E V := sorry

/-- Negative-degree local vanishing implies the eventual owner with bound `dV + max 0 m`. -/
@[stacks 0D6N "negative-to-eventual bridge"]
theorem negative.toEventual
    {E : ModuleDerived.{z} X} {V : X}
    (h : negative X E V) :
    eventual X E V := sorry

/-- A uniform negative-degree bound gives the shifted vanishing estimate used by the eventual
criterion, independently of any covering hypothesis. -/
@[stacks 0D6P "uniform negative shifted-vanishing bridge"]
theorem uniformNegative.vanish_sub
    {E : ModuleDerived.{z} X} {d : ℕ} {B : Set X}
    (h : uniformNegative X E d B) :
    ∀ ⦃V : X⦄, V ∈ B → ∀ p m : ℤ, (d : ℤ) + max 0 m < p →
      IsZero
        (RingedSite.Hom.ModuleDerived.cohomologyOverObject.{z} X V
          ((DerivedCategory.singleFunctor (RingedSite.ModuleCat.{z} X) (0 : ℤ)).obj
            (RingedSite.Hom.ModuleDerived.cohomologySheaf.{z} X E (m - p))) p) := sorry

/-- Uniform negative-degree vanishing implies the uniform eventual bound required by the
truncation comparison criterion. -/
@[stacks 0D6P "uniform negative-to-eventual bridge"]
theorem uniformNegative.toEventual
    {E : ModuleDerived.{z} X} {d : ℕ} {B : Set X}
    (h : uniformNegative X E d B)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B)) :
    ∀ ⦃V : X⦄, V ∈ B → eventual X E V := sorry

end Basis

namespace Comparison

/-- A compatible lower-truncation comparison is an isomorphism under per-object eventual
cohomology vanishing on a covering basis. -/
@[stacks 0D6M "truncation comparison from basiswise eventual vanishing"]
theorem isIso_of_eventual
    (E K : ModuleDerived.{z} X) (c : E ⟶ K)
    (hc : CategoryTheory.DerivedCategory.Truncation.Lower.Comparison.Exists E c)
    (B : Set X)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hvanish : ∀ ⦃V : X⦄, V ∈ B → Basis.eventual X E V) :
    IsIso c := sorry

/-- The comparison criterion specialized to per-object negative-degree vanishing. -/
@[stacks 0D6N "truncation comparison from negative vanishing"]
theorem isIso_of_negative
    (E K : ModuleDerived.{z} X) (c : E ⟶ K)
    (hc : CategoryTheory.DerivedCategory.Truncation.Lower.Comparison.Exists E c)
    (B : Set X)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hvanish : ∀ ⦃V : X⦄, V ∈ B → Basis.negative X E V) :
    IsIso c := sorry

/-- The comparison criterion specialized to a uniform eventual bound. -/
@[stacks 08U3 "uniform truncation comparison"]
theorem isIso_of_uniform
    (E K : ModuleDerived.{z} X) (c : E ⟶ K)
    (hc : CategoryTheory.DerivedCategory.Truncation.Lower.Comparison.Exists E c)
    (pBound : ℤ → ℤ) (B : Set X)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hvanish :
      ∀ ⦃V : X⦄, V ∈ B → ∀ p m : ℤ, pBound m < p →
        IsZero
          (RingedSite.Hom.ModuleDerived.cohomologyOverObject.{z} X V
            ((DerivedCategory.singleFunctor (RingedSite.ModuleCat.{z} X) (0 : ℤ)).obj
              (RingedSite.Hom.ModuleDerived.cohomologySheaf.{z} X E (m - p))) p)) :
    IsIso c := sorry

/-- The comparison criterion specialized to a uniform natural-number negative-degree bound. -/
@[stacks 0D6P "uniform negative truncation comparison"]
theorem isIso_of_uniformNegative
    (E K : ModuleDerived.{z} X) (c : E ⟶ K)
    (hc : CategoryTheory.DerivedCategory.Truncation.Lower.Comparison.Exists E c)
    (d : ℕ) (B : Set X)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hvanish : Basis.uniformNegative X E d B) :
    IsIso c := sorry

end Comparison

namespace Resolution

/-- Stacks 070Q: the canonical map from a complex to the inverse limit of its injective
lower-truncation resolution is a quasi-isomorphism under a uniform basiswise negative bound. -/
@[stacks 070Q]
theorem quasiIso_intoLimit_of_uniformNegative
    (F : CochainComplex (RingedSite.ModuleCat.{z} X) ℤ)
    (S : CochainComplex.LowerTruncation.Resolution
      (isInjective (RingedSite.ModuleCat.{z} X)) F)
    (B : Set X) (d : ℕ)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hvanish : Basis.uniformNegative X (DerivedCategory.Q.obj F) d B) :
    QuasiIso S.intoLimit := sorry

/-- Stacks 070Q: a map into the resolution limit satisfying the stagewise projection equations is
a quasi-isomorphism under the same uniform basiswise negative bound. -/
@[stacks 070Q]
theorem quasiIso_of_comp_π_uniformNegative
    (F : CochainComplex (RingedSite.ModuleCat.{z} X) ℤ)
    (S : CochainComplex.LowerTruncation.Resolution
      (isInjective (RingedSite.ModuleCat.{z} X)) F)
    (γ : F ⟶ limit S.tower)
    (B : Set X) (d : ℕ)
    (hγ : ∀ n : ℕ, γ ≫ limit.π S.tower (op n) = S.fromSource n)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hvanish : Basis.uniformNegative X (DerivedCategory.Q.obj F) d B) :
    QuasiIso γ := sorry

end Resolution

end RingedSite.Hom.ModuleDerived.Limit

end
