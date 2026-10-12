/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map.Basic

/-!
# Projection comparisons for categorical pullback maps

This module owns the canonical comparisons between an induced pullback map followed by either
projection and the corresponding leg of its cospan transformation.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉
universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

variable {X : Type u₁} [Category.{v₁} X]
variable {Y : Type u₂} [Category.{v₂} Y]
variable {Z : Type u₃} [Category.{v₃} Z]
variable {A : Type u₄} [Category.{v₄} A]
variable {B : Type u₅} [Category.{v₅} B]
variable {C : Type u₆} [Category.{v₆} C]

namespace Limits.CategoricalPullback

variable {H : X ⥤ Z} {I : Y ⥤ Z} {F : A ⥤ C} {G : B ⥤ C}

/-- Projecting an induced pullback map to the left gives the left component of the cospan
transformation:

```
                  map ψ
       H ⊡ I ─────────────────▶ F ⊡ G
         │                       │
  π₁ H I │                       │ π₁ F G
         ▼                       ▼
         X ────────────────────▶ A
                  ψ.left
```

For the explicit `CategoricalPullback` model this comparison is definitionally the identity. -/
def mapFstIso (ψ : CatCospanTransform H I F G) :
    map ψ ⋙ π₁ F G ≅ π₁ H I ⋙ ψ.left :=
  Iso.refl _

/-- Projecting an induced pullback map to the right gives the right component of the cospan
transformation:

```
                  map ψ
       H ⊡ I ─────────────────▶ F ⊡ G
         │                       │
  π₂ H I │                       │ π₂ F G
         ▼                       ▼
         Y ────────────────────▶ B
                  ψ.right
```

For the explicit `CategoricalPullback` model this comparison is definitionally the identity. -/
def mapSndIso (ψ : CatCospanTransform H I F G) :
    map ψ ⋙ π₂ F G ≅ π₂ H I ⋙ ψ.right :=
  Iso.refl _

/-- The forward component of the left-projection comparison is the identity. -/
@[simp]
theorem mapFstIso.hom.app (ψ : CatCospanTransform H I F G) (P : H ⊡ I) :
    (mapFstIso ψ).hom.app P = 𝟙 _ := sorry

/-- The inverse component of the left-projection comparison is the identity. -/
@[simp]
theorem mapFstIso.inv.app (ψ : CatCospanTransform H I F G) (P : H ⊡ I) :
    (mapFstIso ψ).inv.app P = 𝟙 _ := sorry

/-- The forward component of the right-projection comparison is the identity. -/
@[simp]
theorem mapSndIso.hom.app (ψ : CatCospanTransform H I F G) (P : H ⊡ I) :
    (mapSndIso ψ).hom.app P = 𝟙 _ := sorry

/-- The inverse component of the right-projection comparison is the identity. -/
@[simp]
theorem mapSndIso.inv.app (ψ : CatCospanTransform H I F G) (P : H ⊡ I) :
    (mapSndIso ψ).inv.app P = 𝟙 _ := sorry

end Limits.CategoricalPullback

end CategoryTheory

/- Axiom audit: both projection comparisons are definitionally identity isomorphisms. -/
