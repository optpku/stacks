/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallAtlas
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Square

/-! # Small, actual étale squares over a morphism of algebraic spaces

Both vertices are indexed by the existing affine atlas sites in universe u.
The edge is a scheme morphism over S, not a selected geometric inverse image.
All morphisms of squares are retained, including those changing atlas lifts.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PullbackFactory.Squares

variable {S : Scheme.{u}}

/-- The actual original-universe atlas site already used for scalar extension. -/
abbrev Site (X : AlgebraicSpace S) :=
  SmallAtlas.Site (AtlasInput.scheme X)
    (AtlasInput.map X)

/-- The actual chart inclusion. -/
def inclusion (X : AlgebraicSpace S) : Site X ⥤ smallEtaleSite X :=
  SmallAtlas.inclusion (AtlasInput.scheme X)
    (AtlasInput.map X)

/-- The induced étale topology on the small chart category. -/
def topology (X : AlgebraicSpace S) : GrothendieckTopology (Site X) :=
  SmallAtlas.topology (AtlasInput.scheme X)
    (AtlasInput.map X)

variable {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- A genuine commuting square whose scheme vertices are u-small indices. -/
structure Square : Type u where
  left : Site X
  right : Site Y
  map : ((inclusion X).obj left).left ⟶ ((inclusion Y).obj right).left
  w : ((inclusion X).obj left).hom ≫ f =
    ofOverMap map ≫ ((inclusion Y).obj right).hom

/-- The corresponding square in the original geometric interface. -/
def Square.geometric (a : Square f) : EtaleSquare f where
  left := (inclusion X).obj a.left
  right := (inclusion Y).obj a.right
  map := a.map
  w := a.w

/-- Morphisms retain the two actual chart maps and their commuting equation. -/
@[ext]
structure Hom (a b : Square f) : Type u where
  left : a.left ⟶ b.left
  right : a.right ⟶ b.right
  w : ((inclusion X).map left).left ≫ b.map =
    a.map ≫ ((inclusion Y).map right).left

instance : Category (Square f) where
  Hom := Hom f
  id a := { left := 𝟙 a.left, right := 𝟙 a.right, w := by simp [inclusion] }
  comp g h :=
    { left := g.left ≫ h.left
      right := g.right ≫ h.right
      w := by
        change (((inclusion X).map g.left).left ≫
          ((inclusion X).map h.left).left) ≫ _ =
          _ ≫ (((inclusion Y).map g.right).left ≫
            ((inclusion Y).map h.right).left)
        rw [Category.assoc, h.w, ← Category.assoc, g.w, Category.assoc] }
  id_comp g := by ext <;> simp
  comp_id g := by ext <;> simp
  assoc g h k := by ext <;> simp [Category.assoc]

/-- Projection onto the X-chart. -/
def source : Square f ⥤ Site X where
  obj a := a.left
  map g := g.left

/-- Projection onto the Y-chart. -/
def target : Square f ⥤ Site Y where
  obj a := a.right
  map g := g.right

@[simp]
theorem geometric_map (a : Square f) : a.geometric.map = a.map := rfl

@[simp]
theorem source_map {a b : Square f} (g : a ⟶ b) :
    (source f).map g = g.left := rfl

@[simp]
theorem target_map {a b : Square f} (g : a ⟶ b) :
    (target f).map g = g.right := rfl

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.Squares
