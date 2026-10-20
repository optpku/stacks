/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing morphisms out of coproducts

A morphism out of an indexed coproduct restricts along any map of index types.  This file owns
that map and its basic computation rules, independently of any particular use of subfamilies.
-/

@[expose] public section

universe v u i j k

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

noncomputable section

/-- Restrict a morphism out of an indexed coproduct along a map of index types. -/
@[stacks 0D07 "(1), restricted coproduct morphism"]
def Sigma.descReindex {ι : Type i} {κ : Type j}
    (F : ι → C) [HasCoproduct F] {X : C}
    (π : (∐ F) ⟶ X) (e : κ → ι) [HasCoproduct (fun a ↦ F (e a))] :
    (∐ fun a ↦ F (e a)) ⟶ X :=
  Sigma.map' e (fun _ ↦ 𝟙 _) ≫ π

/-- A restricted coproduct morphism agrees with the original morphism on every selected
summand. -/
@[reassoc (attr := simp), stacks 0D07 "(1), restricted coproduct injection"]
theorem Sigma.ι_descReindex {ι : Type i} {κ : Type j}
    (F : ι → C) [HasCoproduct F] {X : C}
    (π : (∐ F) ⟶ X) (e : κ → ι) [HasCoproduct (fun a ↦ F (e a))] (a : κ) :
    Sigma.ι (fun b ↦ F (e b)) a ≫ Sigma.descReindex F π e =
      Sigma.ι F (e a) ≫ π := sorry

/-- Restriction along the identity map does not change a coproduct morphism. -/
@[simp, stacks 0D07 "(1), identity restriction"]
theorem Sigma.descReindex_id {ι : Type i}
    (F : ι → C) [HasCoproduct F] {X : C} (π : (∐ F) ⟶ X) :
    Sigma.descReindex F π (fun a ↦ a) = π := sorry

/-- Successive restrictions of a coproduct morphism agree with restriction along the composite
index map. -/
@[stacks 0D07 "(1), composite restriction"]
theorem Sigma.descReindex_comp {ι : Type i} {κ : Type j} {l : Type k}
    (F : ι → C) [HasCoproduct F] {X : C}
    (π : (∐ F) ⟶ X) (e : κ → ι) (d : l → κ)
    [HasCoproduct (fun a ↦ F (e a))] [HasCoproduct (fun b ↦ F (e (d b)))] :
    Sigma.descReindex (fun a ↦ F (e a)) (Sigma.descReindex F π e) d =
      Sigma.descReindex F π (fun b ↦ e (d b)) := sorry

end

end CategoryTheory.Limits
