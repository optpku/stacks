/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap42.Lemma_42_47_9_Additivity
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.VectorBundle

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Derived

/-- Total Chern classes of perfect derived modules are multiplicative under binary
biproducts. -/
theorem totalClass_biprod
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : Theory δ π)
    {E F : RingedSpace.ModuleDerived X.toRingedSpace}
    (perfectE : RingedSpace.ModuleDerived.IsPerfect E)
    (perfectF : RingedSpace.ModuleDerived.IsPerfect F)
    (definedE : IsDefined E) (definedF : IsDefined F) :
    totalClass δ π classes (E ⊞ F) (perfectE.biprod perfectF) (definedE.biprod definedF) =
      ChowCohomology.Nonnegative.Completion.mul δ π
        (totalClass δ π classes E perfectE definedE)
        (totalClass δ π classes F perfectF definedF) := sorry

end AlgebraicGeometry.ChernClass.Derived

namespace AlgebraicGeometry.Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree

/-- A binary biproduct of degree-zero vector bundles of pointwise ranks strictly less
than `p` and `q` is a degree-zero vector bundle of pointwise rank strictly less than
`p + q`. -/
theorem biprod {X : Scheme.{u}}
    {E F : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace} {p q : ℕ}
    (hE : IsVectorBundleOfRankLTInDegree E 0 p)
    (hF : IsVectorBundleOfRankLTInDegree F 0 q) :
    IsVectorBundleOfRankLTInDegree (E ⊞ F) 0 (p + q) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.IsVectorBundleOfRankLTInDegree
