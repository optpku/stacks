/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.ColimitComparison
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.Representatives
import Mathlib.Tactic.CrossRefAttribute

/-!
# Site cohomology from terminal-target hypercovering Cech colimits

This leaf specializes the presheaf-target colimit and comparison APIs to the terminal presheaf.
It exposes the certified comparison with site cohomology and the corresponding representative
and common-refinement criteria without enlarging the imports of the generic representative API.
-/

@[expose] public section

noncomputable section

universe d w v u

namespace CategoryTheory.HypercoveringOf.Cech.Terminal

open Limits

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

section Cohomology

variable [HasWeakSheafify J AddCommGrpCat.{max w v}]

/-- The filtered-colimit model for site cohomology, functorially in the coefficient sheaf. -/
abbrev cohomologyFunctor (i : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  CategoryTheory.HypercoveringOf.Cech.cohomologyFunctor
    (Presheaf.terminal C) i

/-- The filtered-colimit model for site cohomology with a fixed coefficient sheaf. -/
abbrev cohomology (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  (cohomologyFunctor i).obj I

end Cohomology

section Comparison

variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasExt.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]
variable [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{max w v})]
variable [HasDerivedCategory.{d} AddCommGrpCat.{max u v w}]
variable
  [(Sheaf.CohomologyOverPresheaf.homFunctor J
      (Presheaf.terminal C)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf J AddCommGrpCat.{max w v}))]

/-- The standard `Ext` model for site cohomology as a functor of the coefficient sheaf. -/
abbrev siteCohomologyFunctor (i : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{max u v w} :=
  Abelian.extFunctorObj
    (J.freeAbelianSheaf (Presheaf.terminal C) : Sheaf J AddCommGrpCat.{max w v}) i

/-- The standard `Ext` model for site cohomology with a fixed coefficient sheaf. -/
abbrev siteCohomology (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    AddCommGrpCat.{max u v w} :=
  (siteCohomologyFunctor i).obj I

/-- The standard site-cohomology functor raised to the universe of the hypercovering colimit. -/
abbrev liftedSiteCohomologyFunctor (i : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  liftedTargetCohomology (J := J) (Presheaf.terminal C) i

/-- The standard site-cohomology group raised to the universe of the hypercovering colimit. -/
abbrev liftedSiteCohomology
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  (liftedSiteCohomologyFunctor i).obj I

/-- Proposition 25.10.2 (09VZ): a refinement-natural terminal-target comparison whose
induced maps from the hypercovering Cech colimits to site cohomology are isomorphisms. -/
@[stacks 09VZ "certified site comparison"]
structure Comparison (i : ℕ) where
  /-- The derived comparison at every stage, natural in refinements and coefficients. -/
  derived :
    RefinementComparison.Derived (J := J) (G := Presheaf.terminal C)
  /-- The induced comparison is an isomorphism of coefficient functors. -/
  isIso : IsIso
    (CategoryTheory.HypercoveringOf.Cech.comparison (derived.hom i))

attribute [instance] Comparison.isIso

namespace Comparison

/-- The natural transformation underlying a certified terminal-target comparison. -/
abbrev hom {i : ℕ} (c : Comparison (J := J) i) :
    Terminal.cohomologyFunctor (J := J) i ⟶
      Terminal.liftedSiteCohomologyFunctor (J := J) i :=
  CategoryTheory.HypercoveringOf.Cech.comparison (J := J) (c.derived.hom i)

/-- The concrete isomorphism of coefficient functors supplied by a certified comparison. -/
noncomputable def iso {i : ℕ} (c : Comparison (J := J) i) :
    Terminal.cohomologyFunctor (J := J) i ≅
      Terminal.liftedSiteCohomologyFunctor (J := J) i :=
  asIso (hom c)

/-- The map of a certified comparison agrees at each stage with its refinement component. -/
@[reassoc]
theorem stageMap_comp_hom {i : ℕ} (c : Comparison (J := J) i)
    (K : HypercoveringOf J (Presheaf.terminal C))
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    stageMap K I i ≫ (hom c).app I =
      universeLift.{max u v w}.map
        (((c.derived.hom i).app (HypercoveringOf.refinementObject K)).app I) := sorry

end Comparison

/-- Proposition 25.10.2 (09VZ): a certified comparison with site cohomology exists in every
nonnegative degree. -/
@[stacks 09VZ "hypercovering colimit comparison isomorphism"]
theorem comparison_nonempty
    [Limits.HasPullbacks C] [Limits.HasBinaryProducts C] (i : ℕ) :
    Nonempty (Comparison (J := J) i) := sorry

/-- The map from one hypercovering stage to site cohomology is the colimit injection followed
by the concrete comparison induced by the same refinement-natural stage maps. -/
noncomputable def stageToSite
    (c : Comparison (J := J) i)
    (K : HypercoveringOf J (Presheaf.terminal C))
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    stageCohomology K I i ⟶ liftedSiteCohomology I i :=
  stageMap K I i ≫ (Comparison.hom c).app I

/-- A class at one hypercovering stage represents an actual site-cohomology class through the
canonical colimit comparison. -/
@[stacks 09VZ "representation of a site-cohomology class"]
def Represents
    (c : Comparison (J := J) i)
    {K : HypercoveringOf J (Presheaf.terminal C)}
    (xiK : stageCohomology K I i) (xi : liftedSiteCohomology I i) : Prop :=
  stageToSite c K I xiK = xi

/-- Proposition 25.10.2 (09VZ): forgetting stage compatibility from a certified comparison
identifies the site-cohomology functor with the filtered colimit over terminal-target
hypercoverings. -/
@[stacks 09VZ "site cohomology functor as a hypercovering Cech colimit"]
theorem isIsomorphic_siteCohomologyFunctor
    [Limits.HasPullbacks C] [Limits.HasBinaryProducts C] (i : ℕ) :
    IsIsomorphic (cohomologyFunctor (J := J) i)
      (liftedSiteCohomologyFunctor (J := J) i) := sorry

/-- Proposition 25.10.2 (09VZ): evaluation of the functorial comparison identifies site
cohomology with the corresponding filtered colimit. -/
@[stacks 09VZ "site cohomology as a hypercovering Cech colimit"]
theorem isIsomorphic_siteCohomology
    [Limits.HasPullbacks C] [Limits.HasBinaryProducts C]
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    IsIsomorphic (cohomology I i)
      (liftedSiteCohomology I i) := sorry

/-- Proposition 25.10.2 (1): relative to any fixed colimit comparison, every site-cohomology
class has a representative on one hypercovering. -/
@[stacks 09VZ "existence of a hypercovering representative"]
theorem exists_representation
    [Limits.HasPullbacks C] [Limits.HasBinaryProducts C]
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ)
    (c : Comparison (J := J) i) (xi : liftedSiteCohomology I i) :
    ∃ (K : HypercoveringOf J (Presheaf.terminal C))
      (xiK : stageCohomology K I i), Represents c xiK xi := sorry

/-- Proposition 25.10.2 (2): relative to one fixed comparison, two stage classes represent the
same site-cohomology class exactly when they agree after a common hypercovering refinement. -/
@[stacks 09VZ "equality after a common hypercovering refinement"]
theorem stageToSite_eq_iff
    [Limits.HasPullbacks C] [Limits.HasBinaryProducts C]
    (K L : HypercoveringOf J (Presheaf.terminal C))
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ)
    (c : Comparison (J := J) i)
    (xiK : stageCohomology K I i) (xiL : stageCohomology L I i) :
    stageToSite c K I xiK = stageToSite c L I xiL ↔
      EqualAfterRefinement xiK xiL := sorry

end Comparison

end CategoryTheory.HypercoveringOf.Cech.Terminal
