/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Cohomology.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Functor

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The property that a derived module is its degree-`i` cohomology sheaf, with that sheaf
finite locally free of integer rank `r`. -/
def vectorBundleOfRankInDegree (i r : ℤ) : ObjectProperty (ModuleDerived X) :=
  fun E ↦
    IsIsomorphic E ((DerivedCategory.singleFunctor (Modules X) i).obj (cohomologySheaf E i)) ∧
      ∃ n : ℕ, (∀ x : Points X, (n : ℤ) = r) ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank n (cohomologySheaf E i)

/-- A derived module is a vector bundle of integer rank `r` concentrated in degree `i`. -/
abbrev IsVectorBundleOfRankInDegree (E : ModuleDerived X) (i r : ℤ) : Prop :=
  vectorBundleOfRankInDegree i r E

/-- Membership in `vectorBundleOfRankInDegree` is recovery from the degree-`i` cohomology
sheaf together with finite local freeness of the prescribed rank. -/
theorem mem_vectorBundleOfRankInDegree_iff (E : ModuleDerived X) (i r : ℤ) :
    IsVectorBundleOfRankInDegree E i r ↔
      IsIsomorphic E
          ((DerivedCategory.singleFunctor (Modules X) i).obj (cohomologySheaf E i)) ∧
        ∃ n : ℕ, (∀ x : Points X, (n : ℤ) = r) ∧
          SheafOfModules.IsFiniteLocallyFreeOfRank n (cohomologySheaf E i) :=
  Iff.rfl

/-- Being a vector bundle of fixed rank in one degree is invariant under derived
isomorphisms. -/
instance vectorBundleOfRankInDegree_isClosedUnderIsomorphisms (i r : ℤ) :
    (vectorBundleOfRankInDegree i r :
      ObjectProperty (ModuleDerived X)).IsClosedUnderIsomorphisms :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
