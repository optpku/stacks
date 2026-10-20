/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Splitting.Index
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 017P

# Splittings of truncated simplicial objects

This module owns chosen summands and their canonical colimit cofans. It does not impose monicity or
bundle chosen splittings into a category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SimplexCategory SimplexCategory.Truncated SimplexCategory.Truncated.Hom
open scoped SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

namespace Splitting

/-- The object in a truncated splitting selected by the surjection index `A`. -/
@[simp, nolint unusedArguments, stacks 017P "truncated splitting summand family"]
def summand {n : ℕ} (N : Fin (n + 1) → C)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ)
    (A : IndexSet Δ) : C :=
  N A.degree

/-- The canonical cofan built from candidate truncated splitting summands. -/
@[stacks 017P "candidate truncated splitting cofan"]
abbrev cofan' {n : ℕ} (N : Fin (n + 1) → C) (X : SimplicialObject.Truncated C n)
    (ι : ∀ m, N m ⟶ X _⦋m⦌ₙ) (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    Cofan (summand N Δ) :=
  Cofan.mk (X.obj Δ) fun A ↦ ι A.degree ≫ X.map A.map.op

end Splitting

/-- A splitting of a truncated simplicial object consists of chosen summands in every truncated
degree whose canonical cofan indexed by surjections is colimiting. -/
@[stacks 017P]
structure Splitting {n : ℕ} (X : SimplicialObject.Truncated C n) where
  /-- The distinguished summand in each truncated degree. -/
  N : Fin (n + 1) → C
  /-- The map from each distinguished summand into the corresponding degree. -/
  ι : ∀ m, N m ⟶ X _⦋m⦌ₙ
  /-- The canonical cofan gives the required coproduct decomposition in every degree. -/
  isColimit' : ∀ Δ : (SimplexCategory.Truncated n)ᵒᵖ,
    IsColimit (Splitting.cofan' N X ι Δ)

namespace Splitting

variable {n : ℕ} {X : SimplicialObject.Truncated C n} (s : Splitting X)

/-- The canonical cofan associated to a truncated splitting. -/
@[stacks 017P "truncated splitting cofan"]
def cofan (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    Cofan (summand s.N Δ) :=
  Cofan.mk (X.obj Δ) fun A ↦
    s.ι A.degree ≫ X.map A.map.op

/-- The canonical cofan of a truncated splitting is colimiting. -/
@[stacks 017P "truncated splitting cofan colimit"]
def isColimit (Δ : (SimplexCategory.Truncated n)ᵒᵖ) : IsColimit (s.cofan Δ) :=
  s.isColimit' Δ

/-- Formula for a coproduct injection in the cofan of a truncated splitting. -/
@[reassoc, stacks 017P "truncated splitting cofan injection"]
theorem cofan_inj_eq {Δ : (SimplexCategory.Truncated n)ᵒᵖ}
    (A : IndexSet Δ) :
    (s.cofan Δ).inj A =
      s.ι A.degree ≫ X.map A.map.op := sorry

/-- The coproduct injection indexed by the identity surjection is the distinguished summand
map. -/
@[stacks 017P "identity injection of a truncated splitting cofan"]
theorem cofan_inj_id (m : Fin (n + 1)) :
    (s.cofan (op ⦋m⦌ₙ)).inj (IndexSet.id (op ⦋m⦌ₙ)) = s.ι m := sorry

/-- Restrict a morphism from a split truncated simplicial object to its distinguished summand
in degree `m`. -/
@[simp, stacks 017P "restriction to a truncated splitting summand"]
def φ {Y : SimplicialObject.Truncated C n} (f : X ⟶ Y) (m : Fin (n + 1)) :
    s.N m ⟶ Y _⦋m⦌ₙ :=
  s.ι m ≫ f.app (op ⦋m⦌ₙ)

/-- Naturality expresses the restriction of a morphism on every summand of a splitting. -/
@[reassoc, stacks 017P "naturality on truncated splitting summands"]
theorem cofan_inj_comp_app {Y : SimplicialObject.Truncated C n} (f : X ⟶ Y)
    {Δ : (SimplexCategory.Truncated n)ᵒᵖ} (A : IndexSet Δ) :
    (s.cofan Δ).inj A ≫ f.app Δ =
      s.φ f A.degree ≫ Y.map A.map.op := sorry

/-- Two maps from a degree of a split truncated simplicial object are equal when they agree on
every summand. -/
@[stacks 017P "extensionality on a truncated splitting cofan"]
theorem hom_ext' {Z : C} {Δ : (SimplexCategory.Truncated n)ᵒᵖ}
    (f g : X.obj Δ ⟶ Z)
    (h : ∀ A : IndexSet Δ, (s.cofan Δ).inj A ≫ f = (s.cofan Δ).inj A ≫ g) :
    f = g := sorry

/-- Morphisms from a split truncated simplicial object are determined by their restrictions to
the distinguished summands. -/
@[stacks 017P "extensionality for a truncated splitting"]
theorem hom_ext {Y : SimplicialObject.Truncated C n} (f g : X ⟶ Y)
    (h : ∀ m : Fin (n + 1), s.φ f m = s.φ g m) :
    f = g := sorry

/-- Assemble a morphism from a degree of a split truncated simplicial object by specifying it on
every summand. -/
@[stacks 017P "descent from truncated splitting summands"]
def desc {Z : C} (Δ : (SimplexCategory.Truncated n)ᵒᵖ)
    (F : ∀ A : IndexSet Δ, summand s.N Δ A ⟶ Z) : X.obj Δ ⟶ Z :=
  Cofan.IsColimit.desc (s.isColimit Δ) F

/-- The morphism assembled by `desc` restricts to the prescribed map on every summand. -/
@[simp, reassoc, stacks 017P "truncated splitting descent on summands"]
theorem injection_desc {Z : C} (Δ : (SimplexCategory.Truncated n)ᵒᵖ)
    (F : ∀ A : IndexSet Δ, summand s.N Δ A ⟶ Z)
    (A : IndexSet Δ) :
    (s.cofan Δ).inj A ≫ s.desc Δ F = F A := sorry

/-- Coproduct injections in a truncated splitting are natural under epimorphisms of simplex
indices. -/
@[reassoc, stacks 017P "epimorphic naturality of a truncated splitting cofan"]
theorem cofan_inj_epi_naturality
    {Δ₁ Δ₂ : (SimplexCategory.Truncated n)ᵒᵖ} (A : IndexSet Δ₁)
    (p : Δ₁ ⟶ Δ₂) [Epi p.unop] :
    (s.cofan Δ₁).inj A ≫ X.map p =
      (s.cofan Δ₂).inj (A.epiComp p) := sorry

end Splitting

end CategoryTheory.SimplicialObject.Truncated
