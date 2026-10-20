/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Basic
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry.Equivalence
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry.Swap.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetry of locally induced two-fibre products

The selected swap lifts the ordinary pseudo-pullback symmetry. Membership is the only new
proof input; projection, comparison, and involutivity data retain their ambient owners.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace LocallyInduced
namespace TwoFibreProduct

variable {P : ObjectProperty (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable {Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1)}
variable [Q.IsMultiplicative]
variable [BasedCategory.PseudoPullback.HomProperty.IsClosedUnder Q]
variable [projections : Projections.Has (P := P) (Q := Q)]
variable [detected : Projections.IsDetected (P := P) (Q := Q)]
variable {X Y S : Bicategory.LocallyInducedBicategory
  (BasedCategory.{max v vB, max w (max u (max v vB))} C)
  (fun X : P.FullSubbicategory ↦ X.1) Q}

include projections detected in
/-- The ambient swap map satisfies the selected hom property. -/
@[stacks 02XQ "membership of the swap map in a locally induced two-fibre product"]
theorem swap.mem (F : X ⟶ S) (G : Y ⟶ S) :
    Q (apex F G) (apex G F) (BasedCategory.PseudoPullback.swap F.obj G.obj) := sorry
/- Proof strategy: use projection detection together with the strict ambient projection
formulas `BasedCategory.PseudoPullback.swap.fst` and
`BasedCategory.PseudoPullback.swap.snd`. -/

/-- Exchange the two entries of a locally induced two-fibre product. -/
@[stacks 02XQ "swap map of locally induced two-fibre products"]
def swap (F : X ⟶ S) (G : Y ⟶ S) : apex F G ⟶ apex G F :=
  Bicategory.LocallyInducedBicategory.mkHom
    (BasedCategory.PseudoPullback.swap F.obj G.obj) (swap.mem F G)

/-- Forgetting the selected swap recovers the ordinary explicit pseudo-pullback swap. -/
@[simp]
theorem swap.obj (F : X ⟶ S) (G : Y ⟶ S) :
    (swap F G).obj = BasedCategory.PseudoPullback.swap F.obj G.obj := sorry

/-- Swapping exchanges the first projection with the second. -/
@[simp]
theorem swap.fst (F : X ⟶ S) (G : Y ⟶ S) :
    swap F G ≫ CategoryTheory.LocallyInduced.TwoFibreProduct.fst G F =
      CategoryTheory.LocallyInduced.TwoFibreProduct.snd F G := sorry

/-- Swapping exchanges the second projection with the first. -/
@[simp]
theorem swap.snd (F : X ⟶ S) (G : Y ⟶ S) :
    swap F G ≫ CategoryTheory.LocallyInduced.TwoFibreProduct.snd G F =
      CategoryTheory.LocallyInduced.TwoFibreProduct.fst F G := sorry

section ProjectionComparison

/-- Swapping identifies the new first projection with the original second projection. -/
@[stacks 02XQ "first-projection comparison for the locally induced swap"]
noncomputable def swap.fstIso (F : X ⟶ S) (G : Y ⟶ S) :
    swap F G ≫ CategoryTheory.LocallyInduced.TwoFibreProduct.fst G F ≅
      CategoryTheory.LocallyInduced.TwoFibreProduct.snd F G :=
  (Q _ _).isoMk (BasedCategory.PseudoPullback.swap.fstIso F.obj G.obj)

/-- Forgetting the forward first-projection comparison recovers the ambient comparison. -/
@[simp]
theorem swap.fstIso.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.fstIso F G).hom.hom =
      (BasedCategory.PseudoPullback.swap.fstIso F.obj G.obj).hom := sorry

/-- Forgetting the inverse first-projection comparison recovers the ambient comparison. -/
@[simp]
theorem swap.fstIso.inv (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.fstIso F G).inv.hom =
      (BasedCategory.PseudoPullback.swap.fstIso F.obj G.obj).inv := sorry

/-- Swapping identifies the new second projection with the original first projection. -/
@[stacks 02XQ "second-projection comparison for the locally induced swap"]
noncomputable def swap.sndIso (F : X ⟶ S) (G : Y ⟶ S) :
    swap F G ≫ CategoryTheory.LocallyInduced.TwoFibreProduct.snd G F ≅
      CategoryTheory.LocallyInduced.TwoFibreProduct.fst F G :=
  (Q _ _).isoMk (BasedCategory.PseudoPullback.swap.sndIso F.obj G.obj)

/-- Forgetting the forward second-projection comparison recovers the ambient comparison. -/
@[simp]
theorem swap.sndIso.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.sndIso F G).hom.hom =
      (BasedCategory.PseudoPullback.swap.sndIso F.obj G.obj).hom := sorry

/-- Forgetting the inverse second-projection comparison recovers the ambient comparison. -/
@[simp]
theorem swap.sndIso.inv (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.sndIso F G).inv.hom =
      (BasedCategory.PseudoPullback.swap.sndIso F.obj G.obj).inv := sorry

/-- The structural comparison of the swapped locally induced two-fibre product. -/
@[stacks 02XQ "structural comparison for the locally induced swap"]
noncomputable def swap.comparisonIso (F : X ⟶ S) (G : Y ⟶ S) :
    (swap F G ≫ CategoryTheory.LocallyInduced.TwoFibreProduct.fst G F) ≫ G ≅
      (swap F G ≫ CategoryTheory.LocallyInduced.TwoFibreProduct.snd G F) ≫ F :=
  (Q _ _).isoMk (BasedCategory.PseudoPullback.swap.comparisonIso F.obj G.obj)

/-- Forgetting the forward swapped comparison recovers the ambient swapped comparison. -/
@[simp]
theorem swap.comparisonIso.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.comparisonIso F G).hom.hom =
      (BasedCategory.PseudoPullback.swap.comparisonIso F.obj G.obj).hom := sorry

/-- Forgetting the inverse swapped comparison recovers the ambient swapped comparison. -/
@[simp]
theorem swap.comparisonIso.inv (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.comparisonIso F G).inv.hom =
      (BasedCategory.PseudoPullback.swap.comparisonIso F.obj G.obj).inv := sorry

/-- The locally induced lift of `BasedCategory.PseudoPullback.swap.comparisonIso.eq`. -/
theorem swap.comparisonIso.eq (F : X ⟶ S) (G : Y ⟶ S) :
    swap.comparisonIso F G =
      Bicategory.whiskerRightIso (swap.fstIso F G) G ≪≫
        (CategoryTheory.LocallyInduced.TwoFibreProduct.comparisonIso F G).symm ≪≫
          Bicategory.whiskerRightIso (swap.sndIso F G).symm F := sorry

end ProjectionComparison

/-- Swapping twice is the identity morphism. -/
theorem swap.involution.eqId (F : X ⟶ S) (G : Y ⟶ S) :
    swap F G ≫ swap G F = 𝟙 (apex F G) := sorry

/-- Canonical isomorphism witnessing involutivity of the selected swap. -/
@[stacks 02XQ "involutivity isomorphism for the locally induced swap"]
noncomputable def swap.involution.iso (F : X ⟶ S) (G : Y ⟶ S) :
    swap F G ≫ swap G F ≅ 𝟙 (apex F G) :=
  (Q _ _).isoMk (BasedCategory.PseudoPullback.swap.involution.iso F.obj G.obj)

/-- Forgetting the forward involutivity cell recovers the ambient double-swap cell. -/
@[simp]
theorem swap.involution.iso.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.involution.iso F G).hom.hom =
      (BasedCategory.PseudoPullback.swap.involution.iso F.obj G.obj).hom := sorry

/-- Forgetting the inverse involutivity cell recovers the ambient double-swap cell. -/
@[simp]
theorem swap.involution.iso.inv (F : X ⟶ S) (G : Y ⟶ S) :
    (swap.involution.iso F G).inv.hom =
      (BasedCategory.PseudoPullback.swap.involution.iso F.obj G.obj).inv := sorry

end TwoFibreProduct
end LocallyInduced
end CategoryTheory
