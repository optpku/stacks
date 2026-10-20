/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Local

/-!
# Canonical Comparisons Between Local and Colocal Models

Two local targets reached from the same object by morphisms in a fixed morphism property are
canonically isomorphic.  Dually, two colocal sources mapping to the same object are canonically
isomorphic.  The comparison maps are the canonical extension and lifting operations.
-/

@[expose] public section

universe v u

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}

namespace isLocal

/-- A morphism is the canonical extension exactly when it has the prescribed restriction. -/
theorem extension_eq_iff {X Y Z : C} {f : X ⟶ Y} (hf : W f)
    (hZ : W.isLocal Z) (g : X ⟶ Z) (h : Y ⟶ Z) :
    extension hf hZ g = h ↔ f ≫ h = g := sorry

/-- The two canonical comparisons between local models compose to the identity on the first
model. -/
theorem comparison_hom_inv_id {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : W f) (hg : W g) (hY : W.isLocal Y) (hZ : W.isLocal Z) :
    extension hf hZ g ≫ extension hg hY f = 𝟙 Y := sorry

/-- The two canonical comparisons between local models compose to the identity on the second
model. -/
theorem comparison_inv_hom_id {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : W f) (hg : W g) (hY : W.isLocal Y) (hZ : W.isLocal Z) :
    extension hg hY f ≫ extension hf hZ g = 𝟙 Z := sorry

/-- The canonical isomorphism between two local models of the same object. -/
@[stacks 0A8E "canonical comparison of local models"]
noncomputable def comparisonIso {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : W f) (hg : W g) (hY : W.isLocal Y) (hZ : W.isLocal Z) : Y ≅ Z where
  hom := extension hf hZ g
  inv := extension hg hY f
  hom_inv_id := comparison_hom_inv_id hf hg hY hZ
  inv_hom_id := comparison_inv_hom_id hf hg hY hZ

namespace comparisonIso

/-- The forward canonical comparison of local models is the canonical extension. -/
@[simp]
theorem hom {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : W f) (hg : W g) (hY : W.isLocal Y) (hZ : W.isLocal Z) :
    (comparisonIso hf hg hY hZ).hom = extension hf hZ g := sorry

/-- The inverse canonical comparison of local models is the reverse canonical extension. -/
@[simp]
theorem inv {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : W f) (hg : W g) (hY : W.isLocal Y) (hZ : W.isLocal Z) :
    (comparisonIso hf hg hY hZ).inv = extension hg hY f := sorry

/-- The forward canonical comparison restricts to the second local-model map. -/
@[reassoc]
theorem hom_fac {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : W f) (hg : W g) (hY : W.isLocal Y) (hZ : W.isLocal Z) :
    f ≫ (comparisonIso hf hg hY hZ).hom = g := sorry

/-- The inverse canonical comparison restricts to the first local-model map. -/
@[reassoc]
theorem inv_fac {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : W f) (hg : W g) (hY : W.isLocal Y) (hZ : W.isLocal Z) :
    g ≫ (comparisonIso hf hg hY hZ).inv = f := sorry

/-- The canonical comparison of a local model with itself is the identity isomorphism. -/
@[simp]
theorem refl {X Y : C} {f : X ⟶ Y} (hf : W f) (hY : W.isLocal Y) :
    comparisonIso hf hf hY hY = Iso.refl Y := sorry

/-- Reversing the two local models reverses the canonical comparison isomorphism. -/
@[simp]
theorem symm {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}
    (hf : W f) (hg : W g) (hY : W.isLocal Y) (hZ : W.isLocal Z) :
    (comparisonIso hf hg hY hZ).symm = comparisonIso hg hf hZ hY := sorry

/-- Canonical comparisons of local models compose transitively. -/
@[simp]
theorem trans {X Y Z T : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : X ⟶ T}
    (hf : W f) (hg : W g) (hh : W h)
    (hY : W.isLocal Y) (hZ : W.isLocal Z) (hT : W.isLocal T) :
    (comparisonIso hf hg hY hZ).trans (comparisonIso hg hh hZ hT) =
      comparisonIso hf hh hY hT := sorry

end comparisonIso

end isLocal

namespace isColocal

/-- A morphism is the canonical lift exactly when it has the prescribed composite. -/
theorem lift_eq_iff {X Y Z : C} {g : Y ⟶ Z} (hg : W g)
    (hX : W.isColocal X) (f : X ⟶ Z) (h : X ⟶ Y) :
    lift hg hX f = h ↔ h ≫ g = f := sorry

/-- The two canonical comparisons between colocal models compose to the identity on the first
model. -/
theorem comparison_hom_inv_id {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : W f) (hg : W g) (hX : W.isColocal X) (hY : W.isColocal Y) :
    lift hg hX f ≫ lift hf hY g = 𝟙 X := sorry

/-- The two canonical comparisons between colocal models compose to the identity on the second
model. -/
theorem comparison_inv_hom_id {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : W f) (hg : W g) (hX : W.isColocal X) (hY : W.isColocal Y) :
    lift hf hY g ≫ lift hg hX f = 𝟙 Y := sorry

/-- The canonical isomorphism between two colocal models of the same object. -/
@[stacks 0A8E "canonical comparison of colocal models"]
noncomputable def comparisonIso {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : W f) (hg : W g) (hX : W.isColocal X) (hY : W.isColocal Y) : X ≅ Y where
  hom := lift hg hX f
  inv := lift hf hY g
  hom_inv_id := comparison_hom_inv_id hf hg hX hY
  inv_hom_id := comparison_inv_hom_id hf hg hX hY

namespace comparisonIso

/-- The forward canonical comparison of colocal models is the canonical lift. -/
@[simp]
theorem hom {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : W f) (hg : W g) (hX : W.isColocal X) (hY : W.isColocal Y) :
    (comparisonIso hf hg hX hY).hom = lift hg hX f := sorry

/-- The inverse canonical comparison of colocal models is the reverse canonical lift. -/
@[simp]
theorem inv {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : W f) (hg : W g) (hX : W.isColocal X) (hY : W.isColocal Y) :
    (comparisonIso hf hg hX hY).inv = lift hf hY g := sorry

/-- The forward canonical comparison composes to the first colocal-model map. -/
@[reassoc]
theorem hom_fac {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : W f) (hg : W g) (hX : W.isColocal X) (hY : W.isColocal Y) :
    (comparisonIso hf hg hX hY).hom ≫ g = f := sorry

/-- The inverse canonical comparison composes to the second colocal-model map. -/
@[reassoc]
theorem inv_fac {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : W f) (hg : W g) (hX : W.isColocal X) (hY : W.isColocal Y) :
    (comparisonIso hf hg hX hY).inv ≫ f = g := sorry

/-- The canonical comparison of a colocal model with itself is the identity isomorphism. -/
@[simp]
theorem refl {X Z : C} {f : X ⟶ Z} (hf : W f) (hX : W.isColocal X) :
    comparisonIso hf hf hX hX = Iso.refl X := sorry

/-- Reversing the two colocal models reverses the canonical comparison isomorphism. -/
@[simp]
theorem symm {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : W f) (hg : W g) (hX : W.isColocal X) (hY : W.isColocal Y) :
    (comparisonIso hf hg hX hY).symm = comparisonIso hg hf hY hX := sorry

/-- Canonical comparisons of colocal models compose transitively. -/
@[simp]
theorem trans {X Y T Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {h : T ⟶ Z}
    (hf : W f) (hg : W g) (hh : W h)
    (hX : W.isColocal X) (hY : W.isColocal Y) (hT : W.isColocal T) :
    (comparisonIso hf hg hX hY).trans (comparisonIso hg hh hY hT) =
      comparisonIso hf hh hX hT := sorry

end comparisonIso

end isColocal

end CategoryTheory.MorphismProperty
