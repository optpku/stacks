/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Coherence.Unit
import StacksCheckRecall

@[expose] public section

open CategoryTheory MonoidalCategory
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [SymmetricCategory C]

/- Lemma (0HB0) (1). Unit multiplication is invariant under the braiding.
The source's multiplication is `(λ_ (𝟙_ C)).hom`, and ψ is `β_.hom`. -/
@[stacks 0HB0] #check
  (CategoryTheory.MonoidalCategory.braiding_unit_mul :
    (β_ (𝟙_ C) (𝟙_ C)).hom ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom)

/- Lemma (0HB0) (2). Removing the middle unit agrees with braiding it to the
left and then removing it. The source's φ is `α_.inv`, so both composites
start at `X ⊗ (𝟙_ C ⊗ Y)`. -/
@[stacks 0HB0] #check
  (CategoryTheory.MonoidalCategory.tensor_leftUnitor_braiding : ∀ (X Y : C),
    X ◁ (λ_ Y).hom =
      (α_ X (𝟙_ C) Y).inv ≫ ((β_ X (𝟙_ C)).hom ▷ Y) ≫ ((λ_ X).hom ▷ Y))

variable (W X Y Z : C)

/- The final source assertion follows from the two unit identities above and
the canonical pentagon, triangle, hexagon, symmetry, and unitor identities
below. Naturality is supplied by the ambient monoidal and symmetric structures. -/
#check
  (CategoryTheory.MonoidalCategory.pentagon_inv :
    W ◁ (α_ X Y Z).inv ≫ (α_ W (X ⊗ Y) Z).inv ≫ (α_ W X Y).inv ▷ Z =
      (α_ W X (Y ⊗ Z)).inv ≫ (α_ (W ⊗ X) Y Z).inv)

#check
  (CategoryTheory.MonoidalCategory.triangle_assoc_comp_right X Y :
    (α_ X (𝟙_ C) Y).inv ≫ ((ρ_ X).hom ▷ Y) = X ◁ (λ_ Y).hom)

#check
  (CategoryTheory.BraidedCategory.hexagon_reverse X Y Z :
    (α_ X Y Z).inv ≫ (β_ (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      (X ◁ (β_ Y Z).hom) ≫ (α_ X Z Y).inv ≫ ((β_ X Z).hom ▷ Y))

#check
  (CategoryTheory.SymmetricCategory.symmetry X Y :
    (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y))

#check
  (CategoryTheory.MonoidalCategory.unitors_equal : (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom)

#check
  (CategoryTheory.MonoidalCategory.leftUnitor_tensor_hom'' X Y :
    (α_ (𝟙_ C) X Y).hom ≫ (λ_ (X ⊗ Y)).hom = (λ_ X).hom ⊗ₘ 𝟙 Y)

#check
  (CategoryTheory.MonoidalCategory.id_tensor_rightUnitor_inv X Y :
    𝟙 X ⊗ₘ (ρ_ Y).inv = (ρ_ (X ⊗ Y)).inv ≫ (α_ X Y (𝟙_ C)).hom)
