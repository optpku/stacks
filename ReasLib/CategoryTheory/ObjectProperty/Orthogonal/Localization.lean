/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Orthogonal
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.MorphismProperty.Local.Preadditive

/-!
# Orthogonal Objects and Triangulated Localization

For a triangulated object property `P`, its right orthogonal consists exactly of the objects local
with respect to `P.trW`; its left orthogonal is the corresponding colocal class.  This file turns
those characterizations into directly usable Hom equivalences and canonical extension/lifting
operations.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ObjectProperty

open Limits Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {P : ObjectProperty C} [P.IsTriangulated]

namespace rightOrthogonal

/-- A right-orthogonal object is local with respect to the morphisms whose cone belongs to `P`. -/
theorem isLocal (Z : C) (hZ : P.rightOrthogonal Z) : P.trW.isLocal Z := by
  simpa only [isLocal_trW] using hZ

/-- Precomposition by a morphism whose cone belongs to `P`, with a right-orthogonal target, as a
Hom equivalence. -/
@[simps! apply]
noncomputable def homEquiv {X Y Z : C} {f : X ⟶ Y} (hf : P.trW f)
    (hZ : P.rightOrthogonal Z) : (Y ⟶ Z) ≃ (X ⟶ Z) :=
  MorphismProperty.isLocal.homEquiv hf Z
    (Eq.mpr (congrArg (fun Q : ObjectProperty C ↦ Q Z) (isLocal_trW P)) hZ)

/-- Precomposition by a morphism whose cone belongs to `P`, with a right-orthogonal target, as an
additive Hom equivalence. -/
@[stacks 0A8E "additive Hom equivalence for a right-orthogonal object"]
noncomputable def homAddEquiv {X Y Z : C} {f : X ⟶ Y} (hf : P.trW f)
    (hZ : P.rightOrthogonal Z) : (Y ⟶ Z) ≃+ (X ⟶ Z) :=
  MorphismProperty.isLocal.homAddEquiv hf Z
    (Eq.mpr (congrArg (fun Q : ObjectProperty C ↦ Q Z) (isLocal_trW P)) hZ)

/-- The additive right-orthogonal Hom equivalence has the same forward map as `homEquiv`. -/
@[simp]
theorem homAddEquiv_apply {X Y Z : C} {f : X ⟶ Y} (hf : P.trW f)
    (hZ : P.rightOrthogonal Z) (g : Y ⟶ Z) :
    homAddEquiv hf hZ g = homEquiv hf hZ g := rfl

/-- Extend a morphism into a right-orthogonal object across a morphism whose cone belongs to
`P`. -/
noncomputable def extension {X Y Z : C} {f : X ⟶ Y} (hf : P.trW f)
    (hZ : P.rightOrthogonal Z) (g : X ⟶ Z) : Y ⟶ Z :=
  (homEquiv hf hZ).symm g

/-- The inverse additive right-orthogonal Hom equivalence is the canonical extension. -/
@[simp]
theorem homAddEquiv_symm_apply {X Y Z : C} {f : X ⟶ Y} (hf : P.trW f)
    (hZ : P.rightOrthogonal Z) (g : X ⟶ Z) :
    (homAddEquiv hf hZ).symm g = extension hf hZ g := rfl

/-- The canonical right-orthogonal extension restricts to the original morphism. -/
@[reassoc]
theorem extension_fac {X Y Z : C} {f : X ⟶ Y} (hf : P.trW f)
    (hZ : P.rightOrthogonal Z) (g : X ⟶ Z) :
    f ≫ extension hf hZ g = g := by
  exact (homEquiv hf hZ).apply_symm_apply g

/-- A morphism with the defining restriction property is the canonical right-orthogonal
extension. -/
theorem extension_unique {X Y Z : C} {f : X ⟶ Y} (hf : P.trW f)
    (hZ : P.rightOrthogonal Z) (g : X ⟶ Z) {h : Y ⟶ Z} (hh : f ≫ h = g) :
    h = extension hf hZ g := by
  exact (homEquiv hf hZ).apply_eq_iff_eq_symm_apply.mp hh

/-- Right-orthogonal extension is natural under postcomposition between right-orthogonal
targets. -/
theorem extension_comp {X Y Z Z' : C} {f : X ⟶ Y} (hf : P.trW f)
    (hZ : P.rightOrthogonal Z) (hZ' : P.rightOrthogonal Z')
    (g : X ⟶ Z) (k : Z ⟶ Z') :
    extension hf hZ' (g ≫ k) = extension hf hZ g ≫ k := by
  symm
  apply extension_unique hf hZ' (g ≫ k)
  rw [← Category.assoc, extension_fac]

/-- The canonical right-orthogonal extension of zero is zero. -/
@[simp]
theorem extension_zero {X Y Z : C} {f : X ⟶ Y} (hf : P.trW f)
    (hZ : P.rightOrthogonal Z) :
    extension hf hZ (0 : X ⟶ Z) = 0 := by
  symm
  apply extension_unique hf hZ 0
  simp only [comp_zero]

/-- Canonical right-orthogonal extension commutes with addition. -/
@[simp]
theorem extension_add {X Y Z : C} {f : X ⟶ Y} (hf : P.trW f)
    (hZ : P.rightOrthogonal Z) (g k : X ⟶ Z) :
    extension hf hZ (g + k) = extension hf hZ g + extension hf hZ k := by
  symm
  apply extension_unique hf hZ (g + k)
  simp only [Preadditive.comp_add, extension_fac]

/-- Canonical right-orthogonal extension commutes with negation. -/
@[simp]
theorem extension_neg {X Y Z : C} {f : X ⟶ Y} (hf : P.trW f)
    (hZ : P.rightOrthogonal Z) (g : X ⟶ Z) :
    extension hf hZ (-g) = -extension hf hZ g := by
  symm
  apply extension_unique hf hZ (-g)
  simp only [Preadditive.comp_neg, extension_fac]

/-- Canonical right-orthogonal extension commutes with subtraction. -/
@[simp]
theorem extension_sub {X Y Z : C} {f : X ⟶ Y} (hf : P.trW f)
    (hZ : P.rightOrthogonal Z) (g k : X ⟶ Z) :
    extension hf hZ (g - k) = extension hf hZ g - extension hf hZ k := by
  symm
  apply extension_unique hf hZ (g - k)
  simp only [Preadditive.comp_sub, extension_fac]

end rightOrthogonal

namespace leftOrthogonal

/-- A left-orthogonal object is colocal with respect to the morphisms whose cone belongs to
`P`. -/
theorem isColocal (X : C) (hX : P.leftOrthogonal X) : P.trW.isColocal X := by
  simpa only [isColocal_trW] using hX

/-- Postcomposition by a morphism whose cone belongs to `P`, with a left-orthogonal source, as a
Hom equivalence. -/
@[simps! apply]
noncomputable def homEquiv {X Y Z : C} {g : Y ⟶ Z} (hg : P.trW g)
    (hX : P.leftOrthogonal X) : (X ⟶ Y) ≃ (X ⟶ Z) :=
  MorphismProperty.isColocal.homEquiv hg X
    (Eq.mpr (congrArg (fun Q : ObjectProperty C ↦ Q X) (isColocal_trW P)) hX)

/-- Postcomposition by a morphism whose cone belongs to `P`, with a left-orthogonal source, as an
additive Hom equivalence. -/
@[stacks 0A8E "additive Hom equivalence for a left-orthogonal object"]
noncomputable def homAddEquiv {X Y Z : C} {g : Y ⟶ Z} (hg : P.trW g)
    (hX : P.leftOrthogonal X) : (X ⟶ Y) ≃+ (X ⟶ Z) :=
  MorphismProperty.isColocal.homAddEquiv hg X
    (Eq.mpr (congrArg (fun Q : ObjectProperty C ↦ Q X) (isColocal_trW P)) hX)

/-- The additive left-orthogonal Hom equivalence has the same forward map as `homEquiv`. -/
@[simp]
theorem homAddEquiv_apply {X Y Z : C} {g : Y ⟶ Z} (hg : P.trW g)
    (hX : P.leftOrthogonal X) (f : X ⟶ Y) :
    homAddEquiv hg hX f = homEquiv hg hX f := rfl

/-- Lift a morphism from a left-orthogonal object through a morphism whose cone belongs to
`P`. -/
noncomputable def lift {X Y Z : C} {g : Y ⟶ Z} (hg : P.trW g)
    (hX : P.leftOrthogonal X) (f : X ⟶ Z) : X ⟶ Y :=
  (homEquiv hg hX).symm f

/-- The inverse additive left-orthogonal Hom equivalence is the canonical lift. -/
@[simp]
theorem homAddEquiv_symm_apply {X Y Z : C} {g : Y ⟶ Z} (hg : P.trW g)
    (hX : P.leftOrthogonal X) (f : X ⟶ Z) :
    (homAddEquiv hg hX).symm f = lift hg hX f := rfl

/-- The canonical left-orthogonal lift composes to the original morphism. -/
@[reassoc]
theorem lift_fac {X Y Z : C} {g : Y ⟶ Z} (hg : P.trW g)
    (hX : P.leftOrthogonal X) (f : X ⟶ Z) :
    lift hg hX f ≫ g = f := by
  exact (homEquiv hg hX).apply_symm_apply f

/-- A morphism with the defining factorization property is the canonical left-orthogonal lift. -/
theorem lift_unique {X Y Z : C} {g : Y ⟶ Z} (hg : P.trW g)
    (hX : P.leftOrthogonal X) (f : X ⟶ Z) {h : X ⟶ Y} (hh : h ≫ g = f) :
    h = lift hg hX f := by
  exact (homEquiv hg hX).apply_eq_iff_eq_symm_apply.mp hh

/-- Left-orthogonal lifting is natural under precomposition between left-orthogonal sources. -/
theorem comp_lift {X' X Y Z : C} {g : Y ⟶ Z} (hg : P.trW g)
    (hX' : P.leftOrthogonal X') (hX : P.leftOrthogonal X)
    (k : X' ⟶ X) (f : X ⟶ Z) :
    lift hg hX' (k ≫ f) = k ≫ lift hg hX f := by
  symm
  apply lift_unique hg hX' (k ≫ f)
  rw [Category.assoc, lift_fac]

/-- The canonical left-orthogonal lift of zero is zero. -/
@[simp]
theorem lift_zero {X Y Z : C} {g : Y ⟶ Z} (hg : P.trW g)
    (hX : P.leftOrthogonal X) :
    lift hg hX (0 : X ⟶ Z) = 0 := by
  symm
  apply lift_unique hg hX 0
  simp only [zero_comp]

/-- Canonical left-orthogonal lifting commutes with addition. -/
@[simp]
theorem lift_add {X Y Z : C} {g : Y ⟶ Z} (hg : P.trW g)
    (hX : P.leftOrthogonal X) (f k : X ⟶ Z) :
    lift hg hX (f + k) = lift hg hX f + lift hg hX k := by
  symm
  apply lift_unique hg hX (f + k)
  simp only [Preadditive.add_comp, lift_fac]

/-- Canonical left-orthogonal lifting commutes with negation. -/
@[simp]
theorem lift_neg {X Y Z : C} {g : Y ⟶ Z} (hg : P.trW g)
    (hX : P.leftOrthogonal X) (f : X ⟶ Z) :
    lift hg hX (-f) = -lift hg hX f := by
  symm
  apply lift_unique hg hX (-f)
  simp only [Preadditive.neg_comp, lift_fac]

/-- Canonical left-orthogonal lifting commutes with subtraction. -/
@[simp]
theorem lift_sub {X Y Z : C} {g : Y ⟶ Z} (hg : P.trW g)
    (hX : P.leftOrthogonal X) (f k : X ⟶ Z) :
    lift hg hX (f - k) = lift hg hX f - lift hg hX k := by
  symm
  apply lift_unique hg hX (f - k)
  simp only [Preadditive.sub_comp, lift_fac]

end leftOrthogonal

end CategoryTheory.ObjectProperty


