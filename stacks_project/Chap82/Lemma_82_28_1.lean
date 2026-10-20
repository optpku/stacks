module

import StacksCheckRecall
public import stacks_project.Chap82.Lemma_82_28_1_Chern

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
open scoped BigOperators

universe u

/- Lemma 82.28.1 (1): In Situation 82.2.1 let `X / B` be good. Let `E` be a
finite locally free `𝒪_X`-module of rank `r = q + 1`, and let
`(π : P ⟶ X, 𝒪_P(1))` be the associated projective bundle. For every morphism
`g : Y ⟶ X` of good algebraic spaces over `B` there are unique maps
`c_i(E) ∩ - : CH_k(Y) ⟶ CH_{k - i}(Y)` for `i = 0, …, r` such that
`c_0(E) ∩ α = α` and
`∑_{i=0}^r (-1)^i c₁(𝒪_{P'}(1))^i ∩ (π')^* (c_{r-i}(E) ∩ α) = 0` in
`CH_{k-1}(P')`, where `π' : P' ⟶ Y` is the base change of `π` along `g`,
realized as `P(g^* E) ⟶ Y`. -/
@[stacks 0ERY] #check
  (ConstantRankChern.unique :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (E : X.Modules) (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]
      {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
      (c : ∀ i : Fin (q + 2), ∀ k : ℤ,
        Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - i.val))
      (h0 : ∀ k : ℤ, c 0 k =
        ChowCohomology.castChowGroup δ (g ≫ f) (sub_zero k).symm)
      (hrel : ∀ (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k),
        ∑ i : Fin (q + 2),
          (-1 : ℤ) ^ i.val •
            ConstantRankChern.relationTermFamily f δ E q g c k i α = 0)
      (i : Fin (q + 2)) (k : ℤ),
      c i k = ConstantRankChern.capFamily f δ E q i.val g k)

/- Lemma 82.28.1 (2): In Situation 82.2.1 let `X / B` be good. Let `E` be a
finite locally free `𝒪_X`-module of rank `r = q + 1`. The maps of
Lemma 82.28.1 (1) assemble to a bivariant class `c_i(E)` of degree `i` on
`X`, i.e. an identity class in `A^i(X)`. -/
@[stacks 0ERY] #check
  (ConstantRankChern.degree :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (E : X.Modules) (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]
      (i : ℕ) (hi : i ≤ q + 1),
      ChowCohomology.degree δ f i)
