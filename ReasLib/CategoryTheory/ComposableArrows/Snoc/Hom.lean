/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ComposableArrows.Snoc

@[expose] public section

/-!
# Morphisms out of a snoc extension

This leaf complements `ComposableArrows.snoc` with the component family and naturality API for
extending a morphism from the initial segment.  The only compatibility input is the final
commuting square.  This is the right-facing counterpart of the inductive constructors already
available for the left end of `ComposableArrows`.
-/

noncomputable section

open CategoryTheory

universe v u

namespace CategoryTheory
namespace ComposableArrows

variable {C : Type u} [Category.{v} C]

set_option linter.defProp false in
/-- The canonical source identification for a component on the initial segment of a snoc
 extension. -/
def snocCastSourceEq {n : ℕ} (F : ComposableArrows C n) (Y : C) (f : F.right ⟶ Y)
    (i : Fin (n + 1)) :
    (snoc F Y f).obj i.castSucc = F.obj i :=
  Fin.lastCases_castSucc
    (n := n + 1)
    (motive := fun _ : Fin (n + 2) ↦ C)
    (last := Y)
    (cast := fun j ↦ F.obj j)
    i

set_option linter.defProp false in
/-- The canonical target identification for a component on the initial segment. -/
def snocCastTargetEq {n : ℕ} (G : ComposableArrows C (n + 1)) (i : Fin (n + 1)) :
    G.δlast.obj i = G.obj i.castSucc := rfl

set_option linter.defProp false in
/-- The canonical source identification for the final component of a snoc extension. -/
def snocLastSourceEq' {n : ℕ} (F : ComposableArrows C n) (Y : C) (f : F.right ⟶ Y) :
    (snoc F Y f).obj (Fin.last (n + 1)) = Y :=
  Fin.lastCases_last
    (n := n + 1)
    (motive := fun _ : Fin (n + 2) ↦ C)
    (last := Y)
    (cast := fun j ↦ F.obj j)

set_option linter.defProp false in
/-- The canonical target identification for the final component. -/
def snocTargetRightEq {n : ℕ} (G : ComposableArrows C (n + 1)) :
    G.right = G.obj (Fin.last (n + 1)) := rfl

/-- The component on the initial segment of a morphism out of a snoc extension. -/
@[stacks 014M "initial component of a morphism out of a snoc extension"]
def snocCastComponent {n : ℕ} {F : ComposableArrows C n}
    {G : ComposableArrows C (n + 1)} {Y : C} {f : F.right ⟶ Y}
    (φ : F ⟶ G.δlast) (i : Fin (n + 1)) :
    (snoc F Y f).obj i.castSucc ⟶ G.obj i.castSucc :=
  eqToHom (snocCastSourceEq F Y f i) ≫
    φ.app i ≫ eqToHom (snocCastTargetEq G i)

/-- The final component of a morphism out of a snoc extension. -/
@[stacks 014M "final component of a morphism out of a snoc extension"]
def snocLastComponent {n : ℕ} {F : ComposableArrows C n}
    {G : ComposableArrows C (n + 1)} {Y : C} {f : F.right ⟶ Y}
    (g : Y ⟶ G.right) :
    (snoc F Y f).obj (Fin.last (n + 1)) ⟶ G.obj (Fin.last (n + 1)) :=
  eqToHom (snocLastSourceEq' F Y f) ≫ g ≫ eqToHom (snocTargetRightEq G)

/-- The component family determined by a morphism on the initial segment and a final component. -/
@[stacks 014M "component family for a morphism out of a snoc extension"]
def snocComponents {n : ℕ} {F : ComposableArrows C n}
    {G : ComposableArrows C (n + 1)} {Y : C} {f : F.right ⟶ Y}
    (φ : F ⟶ G.δlast) (g : Y ⟶ G.right) :
    ∀ i : Fin (n + 2), (snoc F Y f).obj i ⟶ G.obj i :=
  Fin.lastCases (snocLastComponent (f := f) g)
    (fun i ↦ snocCastComponent (f := f) φ i)

/-- On the initial segment, `snocComponents` is the transported old component. -/
@[simp, stacks 014M "initial-component computation for snocComponents"]
theorem snocComponents_castSucc {n : ℕ} {F : ComposableArrows C n}
    {G : ComposableArrows C (n + 1)} {Y : C} {f : F.right ⟶ Y}
    (φ : F ⟶ G.δlast) (g : Y ⟶ G.right) (i : Fin (n + 1)) :
    snocComponents (f := f) φ g i.castSucc = snocCastComponent (f := f) φ i := sorry

/-- The final member of `snocComponents` is the chosen final component. -/
@[simp, stacks 014M "final-component computation for snocComponents"]
theorem snocComponents_last {n : ℕ} {F : ComposableArrows C n}
    {G : ComposableArrows C (n + 1)} {Y : C} {f : F.right ⟶ Y}
    (φ : F ⟶ G.δlast) (g : Y ⟶ G.right) :
    snocComponents (f := f) φ g (Fin.last (n + 1)) = snocLastComponent (f := f) g := sorry

/-- The component family for a snoc extension is natural once the final square commutes. -/
@[stacks 014M "naturality of the snoc component family"]
theorem snocComponents_naturality {n : ℕ} {F : ComposableArrows C n}
    {G : ComposableArrows C (n + 1)} {Y : C} {f : F.right ⟶ Y}
    (φ : F ⟶ G.δlast) (g : Y ⟶ G.right)
    (h : f ≫ g = φ.app (Fin.last n) ≫ G.map' n (n + 1)) (i : Fin (n + 1)) :
    (snoc F Y f).map' i.1 (i.1 + 1) ≫ snocComponents (f := f) φ g i.succ =
      snocComponents (f := f) φ g i.castSucc ≫ G.map' i.1 (i.1 + 1) := sorry

/-- Extend a morphism on the initial segment across one final commuting square. -/
@[stacks 014M "morphism out of a snoc extension"]
def snocHom {n : ℕ} {F : ComposableArrows C n}
    {G : ComposableArrows C (n + 1)} {Y : C} {f : F.right ⟶ Y}
    (φ : F ⟶ G.δlast) (g : Y ⟶ G.right)
    (h : f ≫ g = φ.app (Fin.last n) ≫ G.map' n (n + 1)) :
    snoc F Y f ⟶ G :=
  ComposableArrows.homMk (snocComponents (f := f) φ g)
    (fun i hi ↦ snocComponents_naturality φ g h ⟨i, hi⟩)

/-- The extended morphism has the transported old component on the initial segment. -/
@[simp, stacks 014M "initial-component computation for snocHom"]
theorem snocHom_app_castSucc {n : ℕ} {F : ComposableArrows C n}
    {G : ComposableArrows C (n + 1)} {Y : C} {f : F.right ⟶ Y}
    (φ : F ⟶ G.δlast) (g : Y ⟶ G.right)
    (h : f ≫ g = φ.app (Fin.last n) ≫ G.map' n (n + 1)) (i : Fin (n + 1)) :
    (snocHom φ g h).app i.castSucc = snocCastComponent (f := f) φ i := sorry

/-- The final component of the extended morphism is the transported chosen map. -/
@[simp, stacks 014M "final-component computation for snocHom"]
theorem snocHom_app_last {n : ℕ} {F : ComposableArrows C n}
    {G : ComposableArrows C (n + 1)} {Y : C} {f : F.right ⟶ Y}
    (φ : F ⟶ G.δlast) (g : Y ⟶ G.right)
    (h : f ≫ g = φ.app (Fin.last n) ≫ G.map' n (n + 1)) :
    (snocHom φ g h).app (Fin.last (n + 1)) = snocLastComponent (f := f) g := sorry

end ComposableArrows
end CategoryTheory
