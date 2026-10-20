module

public import stacks_project.Chap75.Lemma_75_26_4_Locus
public import stacks_project.Chap75.Lemma_75_26_4_Pullback
public import stacks_project.Chap75.Lemma_75_26_4_VectorBundle
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Lemma 75.26.4: A perfect derived module has a canonical open locus where it is a
vector bundle of integer rank `r` placed in degree `i`, characterized by derived pullback. -/
@[stacks 0D20] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPerfect.vectorBundleLocus_spec :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {E : ModuleDerived X}
      (hE : ModuleDerived.IsPerfect E) (i r : ℤ),
      ModuleDerived.IsVectorBundleOfRankInDegree
        ((ModuleDerived.pullback (ModuleDerived.IsPerfect.vectorBundleLocus hE i r).ι).obj E)
        i r ∧
      ∀ {Y : AlgebraicSpace S} (f : Y ⟶ X),
        (∃ g : Y ⟶ (ModuleDerived.IsPerfect.vectorBundleLocus hE i r).X,
          g ≫ (ModuleDerived.IsPerfect.vectorBundleLocus hE i r).ι = f) ↔
        ModuleDerived.IsVectorBundleOfRankInDegree ((ModuleDerived.pullback f).obj E) i r)
