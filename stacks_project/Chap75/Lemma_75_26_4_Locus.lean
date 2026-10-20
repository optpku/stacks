module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.VectorBundleLocus
public import stacks_project.Chap75.Lemma_75_26_4_Pullback

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect.vectorBundleLocus_factor_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X}
    (hE : ModuleDerived.IsPerfect E) (i r : ℤ) {Y : AlgebraicSpace S} (f : Y ⟶ X),
    (∃ g : Y ⟶ (ModuleDerived.IsPerfect.vectorBundleLocus hE i r).X,
      g ≫ (ModuleDerived.IsPerfect.vectorBundleLocus hE i r).ι = f) ↔
    ModuleDerived.IsVectorBundleOfRankInDegree ((ModuleDerived.pullback f).obj E) i r)
