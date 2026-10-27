/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.ConstantRankChern
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.RankGluedChern

/-! # Projective characterization of Chern cap operations -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ChernClass

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (δ : Points B → ℤ) [IsDimensionFunction δ]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (E : X.Modules)

/-- A projective relation term applies the complementary cap, projective pullback,
and a tautological Chern power. At rank zero it is the zero map into the Chow
group of the actual projectivization. -/
def projectiveRelationTerm (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (c : ∀ i : Fin (r + 1), ∀ k : ℤ,
      Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - i.val))
    (k : ℤ) (i : Fin (r + 1)) :
    Hom.chowGroup (g ≫ f) δ k →+
      Hom.chowGroup
        (ProjectiveAtlas.projection ((Modules.pullback g).obj E) ≫ g ≫ f) δ (k - 1) := by
  cases r with
  | zero => exact 0
  | succ q => exact ConstantRankChern.relationTermFamily f δ E q g c k i

/-- At rank zero the projective relation term is the zero additive map. -/
theorem projectiveRelationTerm_zero [SheafOfModules.IsFiniteLocallyFreeOfRank 0 E]
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (c : ∀ i : Fin (0 + 1), ∀ k : ℤ,
      Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - i.val))
    (k : ℤ) (i : Fin (0 + 1)) :
    projectiveRelationTerm δ f E 0 g c k i = 0 := rfl

/-- At successor rank the projective relation term is the complementary cap
followed by the canonical projective pullback and tautological Chern power. -/
theorem projectiveRelationTerm_succ (q : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank (q + 1) E]
    {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (c : ∀ i : Fin (q + 2), ∀ k : ℤ,
      Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - i.val))
    (k : ℤ) (i : Fin (q + 2)) :
    projectiveRelationTerm δ f E (q + 1) g c k i =
      ConstantRankChern.relationTermFamily f δ E q g c k i := rfl

/-- Every Chow class on the projectivization of a rank-zero module vanishes. -/
theorem projective_chow_eq_zero_of_rank_zero
    [SheafOfModules.IsFiniteLocallyFreeOfRank 0 E]
    (k : ℤ) (α : Hom.chowGroup (ProjectiveAtlas.projection E ≫ f) δ k) :
    α = 0 := sorry

variable (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank r E]

/-- On a good test space, the operational Chern class of a constant-rank module
acts by the constant-rank Chern cap of its pullback. -/
theorem chernClass_cap_of_constantRank {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (i : ℕ) (k : ℤ) :
    (chernClass δ f E i).cap g k =
      ConstantRankChern.cap (g ≫ f) δ ((Modules.pullback g).obj E) r i k := sorry

/-- The degree-zero operational Chern cap is the identity with its degree transport. -/
theorem chernClass_cap_zero {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] (k : ℤ) :
    (chernClass δ f E 0).cap g k =
      (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ) (sub_zero k).symm).toAddMonoidHom := sorry

/-- The canonical Chern caps satisfy the alternating tautological relation on
the projectivization of the pulled-back module at every finite rank. -/
theorem projective_relation {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k) :
    ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
      projectiveRelationTerm δ f E r g
        (fun i k => (chernClass δ f E i.val).cap g k) k i α = 0 := sorry

/-- Any additive cap family normalized in degree zero and satisfying the
alternating projective relation agrees pointwise with the canonical Chern caps. -/
theorem unique_projective_caps {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)]
    (c : ∀ i : Fin (r + 1), ∀ k : ℤ,
      Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - i.val))
    (h0 : ∀ k : ℤ, c 0 k =
      (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ) (sub_zero k).symm).toAddMonoidHom)
    (hrel : ∀ (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k),
      ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
        projectiveRelationTerm δ f E r g c k i α = 0)
    (i : Fin (r + 1)) (k : ℤ) :
    c i k = (chernClass δ f E i.val).cap g k := sorry

/-- There is a unique additive cap family normalized in degree zero and
satisfying the alternating tautological projective relation. -/
theorem existsUnique_projective_caps {Y : AlgebraicSpace S} (g : Y ⟶ X)
    [QuasiSeparated (g ≫ f)] [LocallyOfFiniteType (g ≫ f)] :
    ∃! c : ∀ i : Fin (r + 1), ∀ k : ℤ,
      Hom.chowGroup (g ≫ f) δ k →+ Hom.chowGroup (g ≫ f) δ (k - i.val),
      (∀ k : ℤ, c 0 k =
        (AddEquiv.cast (M := Hom.chowGroup (g ≫ f) δ) (sub_zero k).symm).toAddMonoidHom) ∧
      (∀ (k : ℤ) (α : Hom.chowGroup (g ≫ f) δ k),
        ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
          projectiveRelationTerm δ f E r g c k i α = 0) := sorry

end AlgebraicGeometry.AlgebraicSpace.ChernClass
