/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DisplayedCategory.Total

/-!
# Transport for total displayed morphisms

Total morphisms are indexed by their source and target total objects.  This leaf provides the
canonical equality transport for those endpoints and reindexing along equal base arrows.  It
complements the base-arrow and displayed-endpoint transports in `DisplayedCategory.Transport`.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace DisplayedCategory.Total.Hom

variable {D : DisplayedCategory C}

/-- Transport a total morphism along equalities of its source and target objects. -/
@[stacks 015N "endpoint transport for displayed-category total morphisms"]
def cast {X X' Y Y' : DisplayedCategory.Total D}
    (hX : X = X') (hY : Y = Y') (f : X ⟶ Y) : X' ⟶ Y' :=
  hX ▸ hY ▸ f

/-- Endpoint transport is trivial at reflexivity. -/
@[simp, stacks 015N "reflexive endpoint transport for displayed-category totals"]
theorem cast_rfl {X Y : DisplayedCategory.Total D} (f : X ⟶ Y) :
    cast (D := D) rfl rfl f = f := rfl

/-- Successive endpoint transports combine by transitivity. -/
@[stacks 015N "transitive endpoint transport for displayed-category totals"]
theorem cast_trans {X X' X'' Y Y' Y'' : DisplayedCategory.Total D}
    (hX : X = X') (hX' : X' = X'') (hY : Y = Y') (hY' : Y' = Y'')
    (f : X ⟶ Y) :
    cast hX' hY' (cast hX hY f) = cast (hX.trans hX') (hY.trans hY') f := by
  cases hX
  cases hX'
  cases hY
  cases hY'
  rfl

/-- Transporting both endpoints forward and backward recovers the original morphism. -/
@[simp, stacks 015N "inverse endpoint transport for displayed-category totals"]
theorem cast_symm_apply {X X' Y Y' : DisplayedCategory.Total D}
    (hX : X = X') (hY : Y = Y') (f : X ⟶ Y) :
    cast hX.symm hY.symm (cast hX hY f) = f := by
  cases hX
  cases hY
  rfl

/-- Transporting both endpoints backward and forward recovers the target morphism. -/
@[simp, stacks 015N "reverse endpoint transport for displayed-category totals"]
theorem cast_apply_symm {X X' Y Y' : DisplayedCategory.Total D}
    (hX : X = X') (hY : Y = Y') (f : X' ⟶ Y') :
    cast hX hY (cast hX.symm hY.symm f) = f := by
  cases hX
  cases hY
  rfl

/-- Endpoint transport is injective. -/
@[stacks 015N "injectivity of endpoint transport for displayed-category totals"]
theorem cast_injective {X X' Y Y' : DisplayedCategory.Total D}
    (hX : X = X') (hY : Y = Y') :
    Function.Injective (cast hX hY : (X ⟶ Y) → (X' ⟶ Y')) := by
  cases hX
  cases hY
  exact fun _ _ h => h

/-- Equality after a common endpoint transport is equivalent to equality before transport. -/
@[simp, stacks 015N "endpoint-transport equality criterion for displayed-category totals"]
theorem cast_eq_iff {X X' Y Y' : DisplayedCategory.Total D}
    (hX : X = X') (hY : Y = Y') (f g : X ⟶ Y) :
    cast hX hY f = cast hX hY g ↔ f = g :=
  (cast_injective hX hY).eq_iff

/-- Transport a total morphism along an equality of its base morphism. -/
@[stacks 015N "base-arrow transport for displayed-category total morphisms"]
def reindex {X Y : DisplayedCategory.Total D}
    {f : DisplayedCategory.Total.Hom D X Y} {g : X.base ⟶ Y.base}
    (h : f.base = g) : DisplayedCategory.Total.Hom D X Y where
  base := g
  displayed := DisplayedCategory.Hom.cast D h f.displayed

/-- Reindexing stores the prescribed base morphism. -/
@[simp, stacks 015N "base projection of displayed-category total reindexing"]
theorem reindex_base {X Y : DisplayedCategory.Total D}
    {f : X ⟶ Y} {g : X.base ⟶ Y.base} (h : f.base = g) :
    (reindex h).base = g := rfl

/-- The displayed component of a reindexed total morphism is canonical transport. -/
@[simp, stacks 015N "displayed projection of total morphism reindexing"]
theorem reindex_displayed {X Y : DisplayedCategory.Total D}
    {f : X ⟶ Y} {g : X.base ⟶ Y.base} (h : f.base = g) :
    (reindex h).displayed = DisplayedCategory.Hom.cast D h f.displayed := rfl

/-- Reindexing by reflexivity leaves a total morphism unchanged. -/
@[simp, stacks 015N "reflexive base-arrow transport for displayed-category totals"]
theorem reindex_rfl {X Y : DisplayedCategory.Total D} {f : X ⟶ Y} :
    reindex (Eq.refl f.base) = f := rfl

/-- Reindexing a total morphism along any equality of its stored base arrow leaves the ordinary
total-category morphism unchanged. -/
@[simp, stacks 015N "proof-independent base-arrow transport for displayed-category totals"]
theorem reindex_eq {X Y : DisplayedCategory.Total D}
    {f : X ⟶ Y} {g : X.base ⟶ Y.base} (h : f.base = g) :
    reindex (f := f) h = f := by
  cases h
  rfl

/-- Extensionality after reindexing a total morphism along an equality of base arrows. -/
@[ext (iff := false), stacks 015N "reindexed extensionality for displayed-category totals"]
theorem ext_reindex {X Y : DisplayedCategory.Total D}
    {f g : X ⟶ Y} (h_base : f.base = g.base)
    (h_displayed : (reindex h_base).displayed = g.displayed) :
    f = g := by
  obtain ⟨f, φ⟩ := f
  obtain ⟨g, ψ⟩ := g
  cases h_base
  cases h_displayed
  rfl

/-- Equality of total morphisms is detected by displayed components after base reindexing. -/
@[simp, stacks 015N "reindexed extensionality criterion for displayed-category totals"]
theorem ext_reindex_iff {X Y : DisplayedCategory.Total D}
    {f g : X ⟶ Y} (h_base : f.base = g.base) :
    f = g ↔ (reindex h_base).displayed = g.displayed := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    exact ext_reindex h_base h

/-- Successive reindexings combine by transitivity. -/
@[stacks 015N "transitive base-arrow transport for displayed-category totals"]
theorem reindex_trans {X Y : DisplayedCategory.Total D}
    {f : X ⟶ Y} {g h : X.base ⟶ Y.base}
    (e : f.base = g) (e' : g = h) :
    reindex (f := reindex e) e' = reindex (e.trans e') := by
  cases e
  cases e'
  rfl

/-- Reindexing by an equality and then by its inverse recovers the original morphism. -/
@[simp, stacks 015N "inverse base-arrow transport for displayed-category totals"]
theorem reindex_symm {X Y : DisplayedCategory.Total D}
    {f : X ⟶ Y} {g : X.base ⟶ Y.base} (e : f.base = g) :
    reindex (f := reindex e) e.symm = f := by
  cases e
  rfl

/-- Reindexing the left factor of a composite agrees with reindexing the composite. -/
@[stacks 015N "left composition and base-arrow transport"]
theorem reindex_comp_left {W X Y : DisplayedCategory.Total D}
    {f : W ⟶ X} {f' : W.base ⟶ X.base} (g : X ⟶ Y) (e : f.base = f') :
    reindex (f := f ≫ g)
        (congrArg (fun k : W.base ⟶ X.base => k ≫ g.base) e) =
      reindex e ≫ g := by
  cases e
  rfl

/-- Reindexing the right factor of a composite agrees with reindexing the composite. -/
@[stacks 015N "right composition and base-arrow transport"]
theorem reindex_comp_right {W X Y : DisplayedCategory.Total D}
    (f : W ⟶ X) {g : X ⟶ Y} {g' : X.base ⟶ Y.base} (e : g.base = g') :
    reindex (f := f ≫ g)
        (congrArg (fun k : X.base ⟶ Y.base => f.base ≫ k) e) =
      f ≫ reindex e := by
  cases e
  rfl

/-- Reindexing both factors of a composite agrees with composing their reindexed total maps. -/
@[stacks 015N "composition and base-arrow transport for displayed-category totals"]
theorem reindex_comp {W X Y : DisplayedCategory.Total D}
    {f : W ⟶ X} {f' : W.base ⟶ X.base}
    {g : X ⟶ Y} {g' : X.base ⟶ Y.base}
    (e : f.base = f') (e' : g.base = g') :
    reindex (f := f ≫ g)
        ((DisplayedCategory.Total.comp_base f g).trans
          (congrArg₂ (fun a b => a ≫ b) e e')) =
      DisplayedCategory.Total.comp
        (reindex (D := D) (f := f) e)
        (reindex (D := D) (f := g) e') := by
  cases e
  cases e'
  rfl

end DisplayedCategory.Total.Hom

end CategoryTheory
