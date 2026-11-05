module

public import ReasLib.CategoryTheory.MorphismProperty.Local
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Additive Hom Equivalences for Local and Colocal Objects

In a preadditive category, the canonical Hom equivalences associated to local and colocal
objects are additive.  This file exposes the resulting `AddEquiv` structures and the
zero/addition/negation/subtraction calculus for canonical extensions and lifts.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] [Preadditive C] {W : MorphismProperty C}

namespace isLocal

/-- Precomposition by a morphism in `W` preserves addition on Hom sets. -/
theorem homEquiv_add {X Y Z : C} {f : X ⟶ Y} (hf : W f) (hZ : W.isLocal Z)
    (g h : Y ⟶ Z) :
    homEquiv hf Z hZ (g + h) = homEquiv hf Z hZ g + homEquiv hf Z hZ h := sorry

/-- Precomposition by a morphism in `W`, with local target, as an additive Hom equivalence. -/
@[stacks 0A8E "additive Hom equivalence for a local object"]
noncomputable def homAddEquiv {X Y : C} {f : X ⟶ Y} (hf : W f) (Z : C)
    (hZ : W.isLocal Z) : (Y ⟶ Z) ≃+ (X ⟶ Z) :=
  { homEquiv hf Z hZ with
    map_add' := homEquiv_add hf hZ }

/-- The additive local Hom equivalence has the same forward map as `homEquiv`. -/
@[simp]
theorem homAddEquiv_apply {X Y Z : C} {f : X ⟶ Y} (hf : W f)
    (hZ : W.isLocal Z) (g : Y ⟶ Z) :
    homAddEquiv hf Z hZ g = homEquiv hf Z hZ g := sorry

/-- The inverse additive local Hom equivalence is the canonical extension. -/
@[simp]
theorem homAddEquiv_symm_apply {X Y Z : C} {f : X ⟶ Y} (hf : W f)
    (hZ : W.isLocal Z) (g : X ⟶ Z) :
    (homAddEquiv hf Z hZ).symm g = extension hf hZ g := sorry

/-- Precomposition by a morphism in `W`, with local target, sends zero to zero. -/
@[simp]
theorem homEquiv_zero {X Y Z : C} {f : X ⟶ Y} (hf : W f)
    (hZ : W.isLocal Z) :
    homEquiv hf Z hZ (0 : Y ⟶ Z) = 0 := sorry

/-- Precomposition by a morphism in `W`, with local target, commutes with negation. -/
@[simp]
theorem homEquiv_neg {X Y Z : C} {f : X ⟶ Y} (hf : W f)
    (hZ : W.isLocal Z) (g : Y ⟶ Z) :
    homEquiv hf Z hZ (-g) = -homEquiv hf Z hZ g := sorry

/-- Precomposition by a morphism in `W`, with local target, commutes with subtraction. -/
@[simp]
theorem homEquiv_sub {X Y Z : C} {f : X ⟶ Y} (hf : W f)
    (hZ : W.isLocal Z) (g h : Y ⟶ Z) :
    homEquiv hf Z hZ (g - h) = homEquiv hf Z hZ g - homEquiv hf Z hZ h := sorry

/-- The canonical extension of the zero morphism is zero. -/
@[simp]
theorem extension_zero {X Y Z : C} {f : X ⟶ Y} (hf : W f)
    (hZ : W.isLocal Z) :
    extension hf hZ (0 : X ⟶ Z) = 0 := sorry

/-- Canonical extension commutes with addition. -/
@[simp]
theorem extension_add {X Y Z : C} {f : X ⟶ Y} (hf : W f)
    (hZ : W.isLocal Z) (g h : X ⟶ Z) :
    extension hf hZ (g + h) = extension hf hZ g + extension hf hZ h := sorry

/-- Canonical extension commutes with negation. -/
@[simp]
theorem extension_neg {X Y Z : C} {f : X ⟶ Y} (hf : W f)
    (hZ : W.isLocal Z) (g : X ⟶ Z) :
    extension hf hZ (-g) = -extension hf hZ g := sorry

/-- Canonical extension commutes with subtraction. -/
@[simp]
theorem extension_sub {X Y Z : C} {f : X ⟶ Y} (hf : W f)
    (hZ : W.isLocal Z) (g h : X ⟶ Z) :
    extension hf hZ (g - h) = extension hf hZ g - extension hf hZ h := sorry

end isLocal

namespace isColocal

/-- Postcomposition by a morphism in `W` preserves addition on Hom sets. -/
theorem homEquiv_add {X Y Z : C} {g : Y ⟶ Z} (hg : W g) (hX : W.isColocal X)
    (f k : X ⟶ Y) :
    homEquiv hg X hX (f + k) = homEquiv hg X hX f + homEquiv hg X hX k := sorry

/-- Postcomposition by a morphism in `W`, with colocal source, as an additive Hom equivalence. -/
@[stacks 0A8E "additive Hom equivalence for a colocal object"]
noncomputable def homAddEquiv {Y Z : C} {g : Y ⟶ Z} (hg : W g) (X : C)
    (hX : W.isColocal X) : (X ⟶ Y) ≃+ (X ⟶ Z) :=
  { homEquiv hg X hX with
    map_add' := homEquiv_add hg hX }

/-- The additive colocal Hom equivalence has the same forward map as `homEquiv`. -/
@[simp]
theorem homAddEquiv_apply {X Y Z : C} {g : Y ⟶ Z} (hg : W g)
    (hX : W.isColocal X) (f : X ⟶ Y) :
    homAddEquiv hg X hX f = homEquiv hg X hX f := sorry

/-- The inverse additive colocal Hom equivalence is the canonical lift. -/
@[simp]
theorem homAddEquiv_symm_apply {X Y Z : C} {g : Y ⟶ Z} (hg : W g)
    (hX : W.isColocal X) (f : X ⟶ Z) :
    (homAddEquiv hg X hX).symm f = lift hg hX f := sorry

/-- Postcomposition by a morphism in `W`, with colocal source, sends zero to zero. -/
@[simp]
theorem homEquiv_zero {X Y Z : C} {g : Y ⟶ Z} (hg : W g)
    (hX : W.isColocal X) :
    homEquiv hg X hX (0 : X ⟶ Y) = 0 := sorry

/-- Postcomposition by a morphism in `W`, with colocal source, commutes with negation. -/
@[simp]
theorem homEquiv_neg {X Y Z : C} {g : Y ⟶ Z} (hg : W g)
    (hX : W.isColocal X) (f : X ⟶ Y) :
    homEquiv hg X hX (-f) = -homEquiv hg X hX f := sorry

/-- Postcomposition by a morphism in `W`, with colocal source, commutes with subtraction. -/
@[simp]
theorem homEquiv_sub {X Y Z : C} {g : Y ⟶ Z} (hg : W g)
    (hX : W.isColocal X) (f k : X ⟶ Y) :
    homEquiv hg X hX (f - k) = homEquiv hg X hX f - homEquiv hg X hX k := sorry

/-- The canonical lift of the zero morphism is zero. -/
@[simp]
theorem lift_zero {X Y Z : C} {g : Y ⟶ Z} (hg : W g)
    (hX : W.isColocal X) :
    lift hg hX (0 : X ⟶ Z) = 0 := sorry

/-- Canonical lifting commutes with addition. -/
@[simp]
theorem lift_add {X Y Z : C} {g : Y ⟶ Z} (hg : W g)
    (hX : W.isColocal X) (f k : X ⟶ Z) :
    lift hg hX (f + k) = lift hg hX f + lift hg hX k := sorry

/-- Canonical lifting commutes with negation. -/
@[simp]
theorem lift_neg {X Y Z : C} {g : Y ⟶ Z} (hg : W g)
    (hX : W.isColocal X) (f : X ⟶ Z) :
    lift hg hX (-f) = -lift hg hX f := sorry

/-- Canonical lifting commutes with subtraction. -/
@[simp]
theorem lift_sub {X Y Z : C} {g : Y ⟶ Z} (hg : W g)
    (hX : W.isColocal X) (f k : X ⟶ Z) :
    lift hg hX (f - k) = lift hg hX f - lift hg hX k := sorry

end isColocal

end CategoryTheory.MorphismProperty


