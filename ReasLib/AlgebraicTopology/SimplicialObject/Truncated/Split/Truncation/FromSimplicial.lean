/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Splitting.Truncation.FromSimplicial
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Split.Functors
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Split.Truncation.Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 017P

# Truncating bundled split simplicial objects

This module makes finite truncation functorial on bundled split simplicial objects and compares
direct truncation with truncation through an intermediate level.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

namespace Split.truncation

/-- Restrict a bundled split simplicial object to degree `n`. -/
@[stacks 017P "object map for truncating split simplicial objects"]
def obj (S : Split C) (n : ℕ) : Truncated.Split C n :=
  Truncated.Split.mk' (S.s.truncation n)

namespace map

/-- The restricted underlying morphism and restricted summand maps are compatible. -/
@[stacks 017P "morphism compatibility after truncating split simplicial objects"]
theorem comm {S₁ S₂ : Split C} (Φ : S₁ ⟶ S₂) (n : ℕ)
    (m : Fin (n + 1)) :
    (S₁.s.truncation n).ι m ≫
        ((SimplicialObject.truncation n).map Φ.F).app (op ⦋m⦌ₙ) =
      Φ.f m.1 ≫ (S₂.s.truncation n).ι m := sorry

end map

/-- Restrict a morphism of split simplicial objects to degree `n`. -/
@[stacks 017P "morphism map for truncating split simplicial objects"]
def map {S₁ S₂ : Split C} (Φ : S₁ ⟶ S₂) (n : ℕ) :
    obj S₁ n ⟶ obj S₂ n where
  F := (SimplicialObject.truncation n).map Φ.F
  f m := Φ.f m.1
  comm := map.comm Φ n

namespace map

/-- Restricting an identity morphism gives an identity morphism. -/
@[stacks 017P "identity law for truncating split morphisms"]
theorem id (S : Split C) (n : ℕ) :
    map (𝟙 S) n = 𝟙 (obj S n) := sorry

/-- Restriction of split morphisms respects composition. -/
@[stacks 017P "composition law for truncating split morphisms"]
theorem comp {S₁ S₂ S₃ : Split C} (Φ : S₁ ⟶ S₂) (Ψ : S₂ ⟶ S₃) (n : ℕ) :
    map (Φ ≫ Ψ) n = map Φ n ≫ map Ψ n := sorry

end map

end Split.truncation

namespace Split

/-- Truncation defines a functor from split simplicial objects to split truncated simplicial
objects. -/
@[stacks 017P "functorial truncation of split simplicial objects"]
def truncation {C : Type u} [Category.{v} C] (n : ℕ) :
    Split C ⥤ Truncated.Split C n where
  obj S := truncation.obj S n
  map Φ := truncation.map Φ n
  map_id S := truncation.map.id S n
  map_comp Φ Ψ := truncation.map.comp Φ Ψ n

namespace truncation

/-- Formula for the underlying object of functorial truncation. -/
@[simp, stacks 017P "underlying object after functorial truncation"]
theorem obj_X (n : ℕ) (S : Split C) :
    ((Split.truncation (C := C) n).obj S).X =
      (SimplicialObject.truncation n).obj S.X := sorry

/-- Formula for the retained summands under functorial truncation. -/
@[simp, stacks 017P "summands after functorial truncation"]
theorem obj_N {n : ℕ} (S : Split C) (m : Fin (n + 1)) :
    ((Split.truncation (C := C) n).obj S).s.N m = S.s.N m.1 := sorry

/-- Formula for the retained distinguished maps under functorial truncation. -/
@[simp, stacks 017P "summand inclusions after functorial truncation"]
theorem obj_ι {n : ℕ} (S : Split C) (m : Fin (n + 1)) :
    ((Split.truncation (C := C) n).obj S).s.ι m = S.s.ι m.1 := sorry

/-- Formula for the underlying morphism under functorial truncation. -/
@[simp, stacks 017P "underlying morphism after functorial truncation"]
theorem map_F (n : ℕ) {S₁ S₂ : Split C} (Φ : S₁ ⟶ S₂) :
    ((Split.truncation (C := C) n).map Φ).F =
      (SimplicialObject.truncation n).map Φ.F := sorry

/-- Formula for the retained summand maps under functorial truncation. -/
@[simp, stacks 017P "summand maps after functorial truncation"]
theorem map_f {n : ℕ} {S₁ S₂ : Split C}
    (Φ : S₁ ⟶ S₂) (m : Fin (n + 1)) :
    ((Split.truncation (C := C) n).map Φ).f m = Φ.f m.1 := sorry

/-- Forgetting a truncated splitting after restricting it is the ordinary truncation of the
underlying simplicial object. -/
@[simp, stacks 017P "forgetful compatibility for truncating split simplicial objects"]
theorem forget (C : Type u) [Category.{v} C] (n : ℕ) :
    Split.truncation (C := C) n ⋙ Truncated.Split.forget C =
      Split.forget C ⋙ SimplicialObject.truncation n := sorry

/-- Evaluation at a retained summand commutes with truncation of split simplicial objects. -/
@[simp, stacks 017P "summand evaluation after truncating split simplicial objects"]
theorem evalN (C : Type u) [Category.{v} C] {n : ℕ} (m : Fin (n + 1)) :
    Split.truncation (C := C) n ⋙ Truncated.Split.evalN C m =
      Split.evalN C m.1 := sorry

/-- Truncating a split simplicial object first to `n` and then to `m ≤ n` is naturally
isomorphic to truncating it directly to `m`. -/
@[stacks 017P "composition comparison for truncating split simplicial objects"]
def compIso (C : Type u) [Category.{v} C] {n m : ℕ} (h : m ≤ n) :
    Split.truncation (C := C) n ⋙ Truncated.Split.trunc C h ≅
      Split.truncation (C := C) m :=
  Iso.refl _

/-- The forward component of the ambient truncation comparison is the identity. -/
@[simp, stacks 017P "forward component of the ambient truncation comparison"]
theorem compIso_hom_app {n m : ℕ} (h : m ≤ n) (S : Split C) :
    (compIso C h).hom.app S =
      𝟙 ((Split.truncation (C := C) m).obj S) := sorry

/-- The inverse component of the ambient truncation comparison is the identity. -/
@[simp, stacks 017P "inverse component of the ambient truncation comparison"]
theorem compIso_inv_app {n m : ℕ} (h : m ≤ n) (S : Split C) :
    (compIso C h).inv.app S =
      𝟙 ((Split.truncation (C := C) m).obj S) := sorry

end truncation

end Split

end CategoryTheory.SimplicialObject
