/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry.Equivalence
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry.Swap.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetry of full-subbicategory two-fibre products

The selected swap and all of its comparison cells are lifted from the ordinary explicit
pseudo-pullback symmetry. This file adds only the full-subbicategory owner and its forgetful
computations.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]
variable {X Y S : P.FullSubbicategory}

/-- Exchange the two entries of an explicit two-fibre product. On explicit objects it sends
`(x, y, α)` to `(y, x, α.symm)`. -/
@[stacks 0040 "swap map of full-subbicategory two-fibre products"]
def swap (F : X ⟶ S) (G : Y ⟶ S) : apex F G ⟶ apex G F :=
  InducedBicategory.mkHom (PseudoPullback.swap F.hom G.hom)

/-- Forgetting the full-subbicategory swap recovers the explicit pseudo-pullback swap. -/
@[simp]
theorem swap.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (swap F G).hom = PseudoPullback.swap F.hom G.hom := sorry

/-- Swapping exchanges the first projection with the second. -/
@[simp]
theorem swap.fst (F : X ⟶ S) (G : Y ⟶ S) :
    swap F G ≫ TwoFibreProduct.fst G F = TwoFibreProduct.snd F G := sorry

/-- Swapping exchanges the second projection with the first. -/
@[simp]
theorem swap.snd (F : X ⟶ S) (G : Y ⟶ S) :
    swap F G ≫ TwoFibreProduct.snd G F = TwoFibreProduct.fst F G := sorry

/-- Swapping identifies the new first projection with the original second projection. -/
@[stacks 0040 "first-projection comparison for the full-subbicategory swap"]
noncomputable def swap.fstIso (F : X ⟶ S) (G : Y ⟶ S) :
    swap F G ≫ TwoFibreProduct.fst G F ≅ TwoFibreProduct.snd F G :=
  InducedBicategory.isoMk (PseudoPullback.swap.fstIso F.hom G.hom)

/-- Forgetting the forward first-projection comparison recovers the ambient comparison. -/
@[simp]
theorem swap.fstIso.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.fstIso F G).hom.hom =
      (PseudoPullback.swap.fstIso F.hom G.hom).hom := sorry

/-- Forgetting the inverse first-projection comparison recovers the ambient comparison. -/
@[simp]
theorem swap.fstIso.inv (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.fstIso F G).inv.hom =
      (PseudoPullback.swap.fstIso F.hom G.hom).inv := sorry

/-- Swapping identifies the new second projection with the original first projection. -/
@[stacks 0040 "second-projection comparison for the full-subbicategory swap"]
noncomputable def swap.sndIso (F : X ⟶ S) (G : Y ⟶ S) :
    swap F G ≫ TwoFibreProduct.snd G F ≅ TwoFibreProduct.fst F G :=
  InducedBicategory.isoMk (PseudoPullback.swap.sndIso F.hom G.hom)

/-- Forgetting the forward second-projection comparison recovers the ambient comparison. -/
@[simp]
theorem swap.sndIso.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.sndIso F G).hom.hom =
      (PseudoPullback.swap.sndIso F.hom G.hom).hom := sorry

/-- Forgetting the inverse second-projection comparison recovers the ambient comparison. -/
@[simp]
theorem swap.sndIso.inv (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.sndIso F G).inv.hom =
      (PseudoPullback.swap.sndIso F.hom G.hom).inv := sorry

/-- The structural comparison of the swapped two-fibre product. -/
@[stacks 0040 "structural comparison for the full-subbicategory swap"]
noncomputable def swap.comparisonIso (F : X ⟶ S) (G : Y ⟶ S) :
    (swap F G ≫ TwoFibreProduct.fst G F) ≫ G ≅
      (swap F G ≫ TwoFibreProduct.snd G F) ≫ F :=
  InducedBicategory.isoMk (PseudoPullback.swap.comparisonIso F.hom G.hom)

/-- Forgetting the forward swapped comparison recovers the ambient swapped comparison. -/
@[simp]
theorem swap.comparisonIso.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.comparisonIso F G).hom.hom =
      (PseudoPullback.swap.comparisonIso F.hom G.hom).hom := sorry

/-- Forgetting the inverse swapped comparison recovers the ambient swapped comparison. -/
@[simp]
theorem swap.comparisonIso.inv (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.comparisonIso F G).inv.hom =
      (PseudoPullback.swap.comparisonIso F.hom G.hom).inv := sorry

/-- The full-subbicategory lift of `PseudoPullback.swap.comparisonIso.eq`. -/
theorem swap.comparisonIso.eq (F : X ⟶ S) (G : Y ⟶ S) :
    swap.comparisonIso F G =
      whiskerRightIso (swap.fstIso F G) G ≪≫
        (CategoryTheory.TwoFibreProduct.comparisonIso F G).symm ≪≫
          whiskerRightIso (swap.sndIso F G).symm F := sorry

/-- Swapping twice is the identity morphism of the two-fibre-product apex. -/
theorem swap.involution.eqId (F : X ⟶ S) (G : Y ⟶ S) :
    swap F G ≫ swap G F = 𝟙 (apex F G) := sorry

/-- Canonical isomorphism witnessing involutivity of the selected swap. -/
@[stacks 0040 "involutivity isomorphism for the full-subbicategory swap"]
noncomputable def swap.involution.iso (F : X ⟶ S) (G : Y ⟶ S) :
    swap F G ≫ swap G F ≅ 𝟙 (apex F G) :=
  InducedBicategory.isoMk (PseudoPullback.swap.involution.iso F.hom G.hom)

/-- Forgetting the forward involutivity cell recovers the ambient double-swap cell. -/
@[simp]
theorem swap.involution.iso.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.involution.iso F G).hom.hom =
      (PseudoPullback.swap.involution.iso F.hom G.hom).hom := sorry

/-- Forgetting the inverse involutivity cell recovers the ambient double-swap cell. -/
@[simp]
theorem swap.involution.iso.inv (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.involution.iso F G).inv.hom =
      (PseudoPullback.swap.involution.iso F.hom G.hom).inv := sorry

end TwoFibreProduct

end CategoryTheory
