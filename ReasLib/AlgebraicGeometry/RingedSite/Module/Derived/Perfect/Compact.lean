/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Cohomology.Dimension
public import ReasLib.CategoryTheory.Preadditive.CompactObject.Relative
public import ReasLib.CategoryTheory.Sites.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Compactness of perfect derived modules on ringed sites

The cofinal finite-covering hypothesis controls coproducts whose apex is bounded below.  A finite
cohomological-dimension bound at a quasi-compact terminal object upgrades this relative statement
to ordinary compactness.
-/

@[expose] public section

-- Keep these operations on the already specified canonical derived-category model.
-- Local instance justification (defeq pin): ModuleDerived and DerivedCategory.Q must elaborate to the same bundled-ringed-site standard localization; enable the existing reducible moduleCat_hasDerivedCategory owner only for these module comparisons.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [IsGrothendieckAbelian.{w} (RingedSite.ModuleCat.{w} X)]
variable [∀ U : X,
  HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

namespace IsPerfect

/-- Lemma 21.52.7 (09JC) (1): a perfect derived module is compact on ambient coproducts whose
apex is bounded below when every quasi-compact object has a cofinal system of finite coverings by
quasi-compact objects, every such finite covering has quasi-compact pairwise fibre products, and
the site has a quasi-compact terminal object. -/
@[stacks 09JC "(1), bounded-below compactness of perfect objects"]
theorem isCompactOnBoundedBelow_of_cofinalRefinement
    (hQCovers :
      ∀ ⦃U : X⦄ (_ : X.siteTopology.QuasiCompactObject U)
        (𝒰 : SemiRepresentableFamily.Over.{max u v} U),
        𝒰.toSieve ∈ X.siteTopology U →
          ∃ (𝒱 : SemiRepresentableFamily.Over.{max u v} U)
            (_ : Finite 𝒱.index) (_ : 𝒱 ⟶ 𝒰)
            (_ : 𝒱.toSieve ∈ X.siteTopology U),
            ∀ i, X.siteTopology.QuasiCompactObject (𝒱.obj i).left)
    (hQOverlaps :
      ∀ ⦃U : X⦄ (_ : X.siteTopology.QuasiCompactObject U)
        (𝒰 : SemiRepresentableFamily.Over.{max u v} U),
        Finite 𝒰.index → 𝒰.toSieve ∈ X.siteTopology U →
          (∀ i, X.siteTopology.QuasiCompactObject (𝒰.obj i).left) →
            ∃ hpair : 𝒰.toPresieve.HasPairwisePullbacks,
              @pairwiseOverlaps X _ X.siteTopology U 𝒰 hpair)
    (X0 : X) (hX0 : IsTerminal X0)
    (hX0qc : X.siteTopology.QuasiCompactObject X0)
    {K : ModuleDerived.{w} X} (hK : K.IsPerfect) :
    IsCompactObjectOn (t.plus : ObjectProperty (ModuleDerived.{w} X)) K := sorry

/-- Lemma 21.52.7 (09JC) (2): finite module-cohomological dimension at the quasi-compact
terminal object upgrades bounded-below compactness of a perfect derived module to ordinary
compactness, under the same covering and overlap hypotheses as part (1). -/
@[stacks 09JC "(2), compactness of perfect objects"]
theorem isCompactObject_of_finiteDimension
    (hQCovers :
      ∀ ⦃U : X⦄ (_ : X.siteTopology.QuasiCompactObject U)
        (𝒰 : SemiRepresentableFamily.Over.{max u v} U),
        𝒰.toSieve ∈ X.siteTopology U →
          ∃ (𝒱 : SemiRepresentableFamily.Over.{max u v} U)
            (_ : Finite 𝒱.index) (_ : 𝒱 ⟶ 𝒰)
            (_ : 𝒱.toSieve ∈ X.siteTopology U),
            ∀ i, X.siteTopology.QuasiCompactObject (𝒱.obj i).left)
    (hQOverlaps :
      ∀ ⦃U : X⦄ (_ : X.siteTopology.QuasiCompactObject U)
        (𝒰 : SemiRepresentableFamily.Over.{max u v} U),
        Finite 𝒰.index → 𝒰.toSieve ∈ X.siteTopology U →
          (∀ i, X.siteTopology.QuasiCompactObject (𝒰.obj i).left) →
            ∃ hpair : 𝒰.toPresieve.HasPairwisePullbacks,
              @pairwiseOverlaps X _ X.siteTopology U 𝒰 hpair)
    (X0 : X) (hX0 : IsTerminal X0)
    (hX0qc : X.siteTopology.QuasiCompactObject X0)
    {K : ModuleDerived.{w} X} (hK : K.IsPerfect)
    (hfinite : ModuleCohomology.HasFiniteDimension X X0) :
    IsCompactObject K := sorry

end IsPerfect

end RingedSite.Hom.ModuleDerived

end
