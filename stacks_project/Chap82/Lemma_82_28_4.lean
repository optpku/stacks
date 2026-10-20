module

import StacksCheckRecall
public import stacks_project.Chap82.Lemma_82_28_4_Commutation

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
open AlgebraicGeometry.AlgebraicSpace.ChowCohomology

universe u

/- Lemma 82.28.4 (1): In Situation 82.2.1 let `X / B` be good. Let `E` be a
finite locally free `𝒪_X`-module of rank `r = q + 1`. Then the identity class
`c_j(E) ∈ A^j(X)` commutes with every homogeneous class `c ∈ A^p(X)`, as
homogeneous multiplication in `ring δ f`. -/
@[stacks 0ES1] #check
  (AlgebraicGeometry.AlgebraicSpace.ChowCohomology.chernClass_comm :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (E : X.Modules) (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]
      (j : ℕ) (hj : j ≤ q + 1) (p : ℤ) (c : degree δ f p),
      homogeneous δ f j (ConstantRankChern.degree f δ E q j hj) * homogeneous δ f p c =
        homogeneous δ f p c * homogeneous δ f j (ConstantRankChern.degree f δ E q j hj))

/- Lemma 82.28.4 (2): In particular, if `F` is a second finite locally free
`𝒪_X`-module of rank `s + 1`, then
`c_i(E) ∩ c_j(F) ∩ α = c_j(F) ∩ c_i(E) ∩ α` after reindexing along
`k - i - j = k - j - i`. The identity-test case `g = 𝟙 X` recovers the
source packaging in `CH_*(X)`. -/
@[stacks 0ES1] #check
  (AlgebraicGeometry.AlgebraicSpace.ChowCohomology.chernClasses_cap_comm :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (E : X.Modules) (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]
      (F : X.Modules) (s : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (s + 1) F]
      {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
      (i : ℕ) (hi : i ≤ q + 1) (j : ℕ) (hj : j ≤ s + 1)
      (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k),
      (ConstantRankChern.degree f δ E q i hi).cap g (k - j)
          ((ConstantRankChern.degree f δ F s j hj).cap g k α) =
        castChowGroup δ (g ≫ f) (sub_right_comm k (i : ℤ) (j : ℤ))
          ((ConstantRankChern.degree f δ F s j hj).cap g (k - i)
            ((ConstantRankChern.degree f δ E q i hi).cap g k α)))
