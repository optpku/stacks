/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberRank
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

@[expose] public section

/-!
# Vector bundles in a single derived degree

This file defines properties asserting that a derived module is recovered from one cohomology
sheaf, which is finite locally free with either a prescribed rank or a pointwise rank bound.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

variable {X : Scheme.{u}}

/-- The property that a derived module is its degree-`i` cohomology sheaf, with that sheaf
finite locally free of constant integer fiber rank `r`. -/
def vectorBundleOfRankInDegree (i r : ℤ) :
    ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace) :=
  fun E ↦
    IsIsomorphic E
        ((DerivedCategory.singleFunctor X.toRingedSpace.Modules i).obj
          (RingedSpace.ModuleDerived.cohomologySheaf E i)) ∧
      (RingedSpace.ModuleDerived.cohomologySheaf E i).IsFiniteLocallyFree ∧
      ∀ x : X,
        Scheme.Modules.fiberRank (RingedSpace.ModuleDerived.cohomologySheaf E i) x = r

/-- Object-level spelling of membership in `vectorBundleOfRankInDegree`. -/
abbrev IsVectorBundleOfRankInDegree
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (i r : ℤ) : Prop :=
  vectorBundleOfRankInDegree i r E

/-- Membership in `vectorBundleOfRankInDegree` is equivalent to recovery from the degree-`i`
cohomology sheaf together with finite local freeness and the prescribed constant rank. -/
theorem mem_vectorBundleOfRankInDegree_iff
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (i r : ℤ) :
    IsVectorBundleOfRankInDegree E i r ↔
      IsIsomorphic E
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules i).obj
            (RingedSpace.ModuleDerived.cohomologySheaf E i)) ∧
        (RingedSpace.ModuleDerived.cohomologySheaf E i).IsFiniteLocallyFree ∧
        ∀ x : X,
          Scheme.Modules.fiberRank (RingedSpace.ModuleDerived.cohomologySheaf E i) x = r := sorry

/-- Being a vector bundle of fixed rank in one degree is invariant under derived
isomorphisms. -/
instance vectorBundleOfRankInDegree_isClosedUnderIsomorphisms (i r : ℤ) :
    (vectorBundleOfRankInDegree i r :
      ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)).IsClosedUnderIsomorphisms := sorry

/-- The property that a derived module is recovered from its degree-`i` cohomology sheaf,
which is finite locally free and has pointwise fiber rank strictly less than `p`. -/
def vectorBundleOfRankLTInDegree (i : ℤ) (p : ℕ) :
    ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace) :=
  fun E ↦
    IsIsomorphic E
        ((DerivedCategory.singleFunctor X.toRingedSpace.Modules i).obj
          (RingedSpace.ModuleDerived.cohomologySheaf E i)) ∧
      (RingedSpace.ModuleDerived.cohomologySheaf E i).IsFiniteLocallyFree ∧
      ∀ x : X,
        Scheme.Modules.fiberFinrank (RingedSpace.ModuleDerived.cohomologySheaf E i) x < p

/-- Object-level spelling of membership in `vectorBundleOfRankLTInDegree`. -/
abbrev IsVectorBundleOfRankLTInDegree
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (i : ℤ) (p : ℕ) : Prop :=
  vectorBundleOfRankLTInDegree i p E

/-- Membership in `vectorBundleOfRankLTInDegree` expands into its single-degree,
finite-locally-free, and pointwise rank clauses. -/
theorem mem_vectorBundleOfRankLTInDegree_iff
    (E : RingedSpace.ModuleDerived X.toRingedSpace) (i : ℤ) (p : ℕ) :
    IsVectorBundleOfRankLTInDegree E i p ↔
      IsIsomorphic E
          ((DerivedCategory.singleFunctor X.toRingedSpace.Modules i).obj
            (RingedSpace.ModuleDerived.cohomologySheaf E i)) ∧
        (RingedSpace.ModuleDerived.cohomologySheaf E i).IsFiniteLocallyFree ∧
        ∀ x : X,
          Scheme.Modules.fiberFinrank (RingedSpace.ModuleDerived.cohomologySheaf E i) x < p := sorry

/-- The pointwise rank-bounded single-degree property is invariant under derived isomorphisms. -/
instance vectorBundleOfRankLTInDegree_isClosedUnderIsomorphisms (i : ℤ) (p : ℕ) :
    (vectorBundleOfRankLTInDegree i p :
      ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)).IsClosedUnderIsomorphisms := sorry

/-- A zero derived module is a degree-zero vector bundle of rank strictly less than
any positive bound. -/
theorem rankBound_of_isZero
    {E : RingedSpace.ModuleDerived X.toRingedSpace}
    (hE : CategoryTheory.Limits.IsZero E) {p : ℕ} (hp : 0 < p) :
    IsVectorBundleOfRankLTInDegree E 0 p := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
