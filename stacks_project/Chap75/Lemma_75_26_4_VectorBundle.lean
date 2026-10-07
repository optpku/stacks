module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh

/-!
# Vector bundles in a single derived degree on algebraic spaces

A derived `𝒪_X`-module is a vector bundle of rank `r` placed in degree `i` when it is
recovered from its degree-`i` cohomology sheaf, and that sheaf is finite locally free of
rank `r`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The degree-`i` cohomology sheaf of a derived `𝒪_X`-module. -/
abbrev cohomologySheaf (E : ModuleDerived X) (i : ℤ) : X.Modules :=
  (DerivedCategory.homologyFunctor (Modules X) i).obj E

/-- The degree-`i` cohomology sheaf is the homology functor applied to `E`. -/
theorem cohomologySheaf_eq (E : ModuleDerived X) (i : ℤ) :
    cohomologySheaf E i = (DerivedCategory.homologyFunctor (Modules X) i).obj E :=
  sorry

/-- The property that a derived module is its degree-`i` cohomology sheaf, with that sheaf
finite locally free of integer rank `r`. -/
def vectorBundleOfRankInDegree (i r : ℤ) : ObjectProperty (ModuleDerived X) :=
  fun E ↦
    IsIsomorphic E ((DerivedCategory.singleFunctor (Modules X) i).obj (cohomologySheaf E i)) ∧
      ∃ n : ℕ, (n : ℤ) = r ∧ SheafOfModules.IsFiniteLocallyFreeOfRank n (cohomologySheaf E i)

/-- Object-level spelling of membership in `vectorBundleOfRankInDegree`. -/
abbrev IsVectorBundleOfRankInDegree (E : ModuleDerived X) (i r : ℤ) : Prop :=
  vectorBundleOfRankInDegree i r E

/-- Membership in `vectorBundleOfRankInDegree` is recovery from the degree-`i` cohomology
sheaf together with finite local freeness of the prescribed rank. -/
theorem mem_vectorBundleOfRankInDegree_iff (E : ModuleDerived X) (i r : ℤ) :
    IsVectorBundleOfRankInDegree E i r ↔
      IsIsomorphic E
          ((DerivedCategory.singleFunctor (Modules X) i).obj (cohomologySheaf E i)) ∧
        ∃ n : ℕ, (n : ℤ) = r ∧
          SheafOfModules.IsFiniteLocallyFreeOfRank n (cohomologySheaf E i) :=
  sorry

/-- Being a vector bundle of fixed rank in one degree is invariant under derived
isomorphisms. -/
instance vectorBundleOfRankInDegree_isClosedUnderIsomorphisms (i r : ℤ) :
    (vectorBundleOfRankInDegree i r :
      ObjectProperty (ModuleDerived X)).IsClosedUnderIsomorphisms :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
