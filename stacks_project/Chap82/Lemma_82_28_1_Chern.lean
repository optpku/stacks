/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.HigherChern
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ProjectiveBaseChange
public import stacks_project.Chap82.Definition_82_26_2_ChowCohomology

/-! Constant-rank identity Chern classes, characterized on every good test. -/
@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Pullback of modules preserves finite local freeness of a prescribed rank. -/
instance pullback_isFiniteLocallyFreeOfRank (g : Y ⟶ X) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank r E] :
    SheafOfModules.IsFiniteLocallyFreeOfRank r ((pullback g).obj E) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern

open HigherChern

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (E : X.Modules) (q : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]

/-- On each good test `g : Y ⟶ X`, cap with the constant-rank Chern class of `g^* E`. -/
def capFamily (i : ℕ) : ChowCohomology.CapFamily δ f i :=
  fun {Y} g _ _ k ↦
    cap (g ≫ f) δ ((Modules.pullback g).obj E) (q + 1) i k

/-- Unfolding of `capFamily` as the constant-rank Chern cap of the pulled-back module. -/
theorem capFamily_apply {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (i : ℕ) (k : ℤ) :
    capFamily f δ E q i g k =
      cap (g ≫ f) δ ((Modules.pullback g).obj E) (q + 1) i k :=
  rfl

/-- The degree-zero constant-rank Chern cap is the identity on Chow groups. -/
theorem cap_zero {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    capFamily f δ E q 0 g k =
      ChowCohomology.castChowGroup δ (g ≫ f) (sub_zero k).symm :=
  sorry

/-- The characterizing alternating relation after base change to `P(g^* E)`. -/
theorem source_relation {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k) :
    ∑ i : Fin (q + 2),
        (-1 : ℤ) ^ i.val •
          relationTerm (g ≫ f) δ ((Modules.pullback g).obj E) q k i α = 0 :=
  sorry

/-- The `i`-th summand of the characterizing relation on `P(g^* E)`, for a
candidate family of caps. -/
def relationTermFamily {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (c : ∀ i : Fin (q + 2), ∀ k : ℤ,
      Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - i.val))
    (k : ℤ) (i : Fin (q + 2)) :
    Hom.chowGroup (g ≫ f) δ k →+
      Hom.chowGroup
        (ProjectiveAtlas.projection ((Modules.pullback g).obj E) ≫ g ≫ f) δ (k - 1) :=
  (ChowCohomology.castChowGroup δ
      (ProjectiveAtlas.projection ((Modules.pullback g).obj E) ≫ g ≫ f)
      (show ((k - i.rev.val) + q) - i.val = k - 1 by
        have hi := i.isLt
        simp only [Fin.val_rev]
        omega)).comp
    ((FirstChernChow.power
        (ProjectiveAtlas.projection ((Modules.pullback g).obj E) ≫ g ≫ f) δ
        (TautologicalDescent.O1 ((Modules.pullback g).obj E)) i.val
        ((k - i.rev.val) + q)).comp
      ((ProjectiveFormulaMap.pullback (g ≫ f) δ
          (ProjectiveAtlas.projection ((Modules.pullback g).obj E)) q
          (k - i.rev.val)).comp
        (c i.rev k)))

/-- Evaluating `relationTermFamily` is the displayed composite
`c₁(𝒪_{P'}(1))^i ∩ (π')^* (c_{r-i} ∩ -)`. -/
theorem relationTermFamily_apply {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (c : ∀ i : Fin (q + 2), ∀ k : ℤ,
      Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - i.val))
    (k : ℤ) (i : Fin (q + 2)) (α : Hom.chowGroup (g ≫ f) δ k) :
    relationTermFamily f δ E q g c k i α =
      ChowCohomology.castChowGroup δ
        (ProjectiveAtlas.projection ((Modules.pullback g).obj E) ≫ g ≫ f)
        (show ((k - i.rev.val) + q) - i.val = k - 1 by
          have hi := i.isLt
          simp only [Fin.val_rev]
          omega)
        (FirstChernChow.power
          (ProjectiveAtlas.projection ((Modules.pullback g).obj E) ≫ g ≫ f) δ
          (TautologicalDescent.O1 ((Modules.pullback g).obj E)) i.val
          ((k - i.rev.val) + q)
          (ProjectiveFormulaMap.pullback (g ≫ f) δ
            (ProjectiveAtlas.projection ((Modules.pullback g).obj E)) q
            (k - i.rev.val) (c i.rev k α))) :=
  rfl

/-- On a good test, any family with `c_0 = id` and the characterizing
`P(g^* E)`-relation agrees with `capFamily`. -/
theorem unique {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (c : ∀ i : Fin (q + 2), ∀ k : ℤ,
      Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - i.val))
    (h0 : ∀ k : ℤ, c 0 k =
      ChowCohomology.castChowGroup δ (g ≫ f) (sub_zero k).symm)
    (hrel : ∀ (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k),
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val • relationTermFamily f δ E q g c k i α = 0)
    (i : Fin (q + 2)) (k : ℤ) :
    c i k = capFamily f δ E q i.val g k :=
  sorry

/-- Proper-pushforward compatibility of constant-rank Chern caps. -/
theorem capFamily_proper (i : ℕ) :
    ChowCohomology.CompatibleWithProperPushforward δ f (capFamily f δ E q i) :=
  sorry

/-- Flat-pullback compatibility of constant-rank Chern caps. -/
theorem capFamily_flat (i : ℕ) :
    ChowCohomology.CompatibleWithFlatPullback δ f (capFamily f δ E q i) :=
  sorry

/-- Cartier–Gysin compatibility of constant-rank Chern caps. -/
theorem capFamily_gysin (i : ℕ) :
    ChowCohomology.CompatibleWithCartierGysin δ f (capFamily f δ E q i) :=
  sorry

/-- The degree-`i` identity bivariant class `c_i(E) ∈ A^i(X)` for
`0 ≤ i ≤ q + 1`. -/
def degree (i : ℕ) (hi : i ≤ q + 1) : ChowCohomology.degree δ f i :=
  ChowCohomology.ofCap δ f (capFamily f δ E q i)
    (capFamily_proper f δ E q i) (capFamily_flat f δ E q i)
    (capFamily_gysin f δ E q i)

/-- The cap action of `degree` is `capFamily`. -/
theorem degree_cap (i : ℕ) (hi : i ≤ q + 1) {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (degree f δ E q i hi).cap g k = capFamily f δ E q i g k :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern
