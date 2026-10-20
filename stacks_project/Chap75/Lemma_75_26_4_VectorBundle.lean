module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.VectorBundle

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.mem_vectorBundleOfRankInDegree_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (E : ModuleDerived X) (i r : ℤ),
    ModuleDerived.IsVectorBundleOfRankInDegree E i r ↔
      IsIsomorphic E ((DerivedCategory.singleFunctor (Modules X) i).obj
        (ModuleDerived.cohomologySheaf E i)) ∧
      ∃ n : ℕ, (∀ x : Points X, (n : ℤ) = r) ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank n (ModuleDerived.cohomologySheaf E i))
