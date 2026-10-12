/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Splitting.Truncation.Restriction
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Split.Functors
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 017P

# Restricting bundled split objects between truncation levels

This module makes restriction along `m ≤ n` functorial on bundled split truncated simplicial
objects and records its identity, composition, forgetful, and evaluation comparisons.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

namespace Split.trunc

/-- Restrict a bundled split `n`-truncated simplicial object to level `m ≤ n`. -/
@[stacks 017P "object map for further truncating split simplicial objects"]
def obj {n m : ℕ} (S : Split C n) (h : m ≤ n) : Split C m :=
  Split.mk' (S.s.trunc h)

namespace map

/-- The restricted underlying morphism and retained summand maps are compatible. -/
@[stacks 017P "morphism compatibility after further truncating split simplicial objects"]
theorem comm {n m : ℕ} {S₁ S₂ : Split C n} (Φ : S₁ ⟶ S₂)
    (h : m ≤ n) (i : Fin (m + 1)) :
    (S₁.s.trunc h).ι i ≫
        ((Truncated.trunc C n m h).map Φ.F).app (op ⦋i⦌ₘ) =
      Φ.f (Fin.castLE (Nat.succ_le_succ h) i) ≫ (S₂.s.trunc h).ι i := sorry

end map

/-- Restrict a morphism of split `n`-truncated simplicial objects to level `m ≤ n`. -/
@[stacks 017P "morphism map for further truncating split simplicial objects"]
def map {n m : ℕ} {S₁ S₂ : Split C n} (Φ : S₁ ⟶ S₂)
    (h : m ≤ n) : obj S₁ h ⟶ obj S₂ h where
  F := (Truncated.trunc C n m h).map Φ.F
  f i := Φ.f (Fin.castLE (Nat.succ_le_succ h) i)
  comm := map.comm Φ h

namespace map

/-- Further truncation sends identity morphisms to identity morphisms. -/
@[stacks 017P "identity law for further truncating split morphisms"]
theorem id {n m : ℕ} (S : Split C n) (h : m ≤ n) :
    map (𝟙 S) h = 𝟙 (obj S h) := sorry

/-- Further truncation respects composition of split morphisms. -/
@[stacks 017P "composition law for further truncating split morphisms"]
theorem comp {n m : ℕ} {S₁ S₂ S₃ : Split C n}
    (Φ : S₁ ⟶ S₂) (Ψ : S₂ ⟶ S₃) (h : m ≤ n) :
    map (Φ ≫ Ψ) h = map Φ h ≫ map Ψ h := sorry

end map

end Split.trunc

namespace Split

/-- Further truncation defines a functor between categories of split truncated simplicial
objects. -/
@[stacks 017P "functorial further truncation of split simplicial objects"]
def trunc (C : Type u) [Category.{v} C] {n m : ℕ} (h : m ≤ n) :
    Split C n ⥤ Split C m where
  obj S := trunc.obj S h
  map Φ := trunc.map Φ h
  map_id S := trunc.map.id S h
  map_comp Φ Ψ := trunc.map.comp Φ Ψ h

namespace trunc

/-- Formula for the underlying object of functorial further truncation. -/
@[simp, stacks 017P "underlying object after functorial further truncation"]
theorem obj_X {n m : ℕ} (h : m ≤ n) (S : Split C n) :
    ((Split.trunc C h).obj S).X = (Truncated.trunc C n m h).obj S.X := sorry

/-- Formula for retained summands under functorial further truncation. -/
@[simp, stacks 017P "summands after functorial further truncation"]
theorem obj_N {n m : ℕ} (h : m ≤ n) (S : Split C n) (i : Fin (m + 1)) :
    ((Split.trunc C h).obj S).s.N i =
      S.s.N (Fin.castLE (Nat.succ_le_succ h) i) := sorry

/-- Formula for retained distinguished maps under functorial further truncation. -/
@[simp, stacks 017P "summand inclusions after functorial further truncation"]
theorem obj_ι {n m : ℕ} (h : m ≤ n) (S : Split C n) (i : Fin (m + 1)) :
    ((Split.trunc C h).obj S).s.ι i =
      S.s.ι (Fin.castLE (Nat.succ_le_succ h) i) := sorry

/-- Formula for the underlying morphism under functorial further truncation. -/
@[simp, stacks 017P "underlying morphism after functorial further truncation"]
theorem map_F {n m : ℕ} (h : m ≤ n) {S₁ S₂ : Split C n} (Φ : S₁ ⟶ S₂) :
    ((Split.trunc C h).map Φ).F = (Truncated.trunc C n m h).map Φ.F := sorry

/-- Formula for retained summand maps under functorial further truncation. -/
@[simp, stacks 017P "summand maps after functorial further truncation"]
theorem map_f {n m : ℕ} (h : m ≤ n) {S₁ S₂ : Split C n}
    (Φ : S₁ ⟶ S₂) (i : Fin (m + 1)) :
    ((Split.trunc C h).map Φ).f i =
      Φ.f (Fin.castLE (Nat.succ_le_succ h) i) := sorry

/-- Forgetting a further-truncated splitting agrees with further truncating the underlying
simplicial object. -/
@[simp, stacks 017P "forgetful compatibility for further truncating split simplicial objects"]
theorem forget (C : Type u) [Category.{v} C] {n m : ℕ} (h : m ≤ n) :
    Split.trunc C h ⋙ Split.forget C =
      Split.forget C ⋙ Truncated.trunc C n m h := sorry

/-- Evaluation at a retained summand commutes with further truncation. -/
@[simp, stacks 017P "summand evaluation after further truncating split simplicial objects"]
theorem evalN (C : Type u) [Category.{v} C] {n m : ℕ} (h : m ≤ n)
    (i : Fin (m + 1)) :
    Split.trunc C h ⋙ Split.evalN C i =
      Split.evalN C (Fin.castLE (Nat.succ_le_succ h) i) := sorry

/-- Functorial further truncation along the identity comparison is naturally the identity
functor. -/
@[stacks 017P "identity comparison for functorial further truncation"]
def idIso (C : Type u) [Category.{v} C] (n : ℕ) :
    Split.trunc C (le_refl n) ≅ 𝟭 (Split C n) :=
  Iso.refl _

/-- The forward component of the identity truncation comparison is the identity. -/
@[simp, stacks 017P "forward component of the identity truncation comparison"]
theorem idIso_hom_app {n : ℕ} (S : Split C n) :
    (idIso C n).hom.app S = 𝟙 S := sorry

/-- The inverse component of the identity truncation comparison is the identity. -/
@[simp, stacks 017P "inverse component of the identity truncation comparison"]
theorem idIso_inv_app {n : ℕ} (S : Split C n) :
    (idIso C n).inv.app S = 𝟙 S := sorry

/-- Successive functorial further truncations are naturally isomorphic to truncation along the
composite comparison. -/
@[stacks 017P "composition comparison for functorial further truncation"]
def compIso (C : Type u) [Category.{v} C] {n m l : ℕ}
    (h : m ≤ n) (g : l ≤ m) :
    Split.trunc C h ⋙ Split.trunc C g ≅ Split.trunc C (g.trans h) :=
  Iso.refl _

/-- The forward component of the composite truncation comparison is the identity. -/
@[simp, stacks 017P "forward component of the composite truncation comparison"]
theorem compIso_hom_app {n m l : ℕ} (h : m ≤ n) (g : l ≤ m)
    (S : Split C n) :
    (compIso C h g).hom.app S =
      𝟙 ((Split.trunc C (g.trans h)).obj S) := sorry

/-- The inverse component of the composite truncation comparison is the identity. -/
@[simp, stacks 017P "inverse component of the composite truncation comparison"]
theorem compIso_inv_app {n m l : ℕ} (h : m ≤ n) (g : l ≤ m)
    (S : Split C n) :
    (compIso C h g).inv.app S =
      𝟙 ((Split.trunc C (g.trans h)).obj S) := sorry

end trunc

end Split

end CategoryTheory.SimplicialObject.Truncated
