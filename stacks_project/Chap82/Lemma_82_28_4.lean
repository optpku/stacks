/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
open AlgebraicGeometry.AlgebraicSpace.OperationalChow

universe u

/- Lemma 82.28.4 (1): In Situation 82.2.1 let `X / B` be good. Let `E` be a
finite locally free `𝒪_X`-module of rank `r`. Then the identity class
`c_j(E) ∈ A^j(X)` commutes with every homogeneous class `c ∈ A^p(X)`, as
homogeneous multiplication in `ring δ f`. -/
@[stacks 0ES1] #check
  (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern.comm :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
      (j : ℕ) (hj : j ≤ r) (p : ℤ) (c : OperationalChow δ f p),
      homogeneous δ f j (ConstantRankChern.degreeOfRank f δ E r j hj) * homogeneous δ f p c =
        homogeneous δ f p c * homogeneous δ f j (ConstantRankChern.degreeOfRank f δ E r j hj))

/- Lemma 82.28.4 (2): In particular, if `F` is a second finite locally free
`𝒪_X`-module of rank `s`, then
`c_i(E) ∩ c_j(F) ∩ α = c_j(F) ∩ c_i(E) ∩ α` after reindexing along
`k - i - j = k - j - i`. The identity-test case `g = 𝟙 X` recovers the
source packaging in `CH_*(X)`. -/
@[stacks 0ES1] #check
  (AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern.classes_cap_comm :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B]
      (δ : Points B → ℤ) [IsDimensionFunction δ]
      (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
      (E : X.Modules) (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
      (F : X.Modules) (s : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank s F]
      {Y : AlgebraicSpace S} (g : Y ⟶ X)
      [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
      (i : ℕ) (hi : i ≤ r) (j : ℕ) (hj : j ≤ s)
      (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k),
      (ConstantRankChern.degreeOfRank f δ E r i hi).cap g (k - j)
          ((ConstantRankChern.degreeOfRank f δ F s j hj).cap g k α) =
        (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ)
          (sub_right_comm k (i : ℤ) (j : ℤ))).toAddMonoidHom
          ((ConstantRankChern.degreeOfRank f δ F s j hj).cap g (k - i)
            ((ConstantRankChern.degreeOfRank f δ E r i hi).cap g k α)))
