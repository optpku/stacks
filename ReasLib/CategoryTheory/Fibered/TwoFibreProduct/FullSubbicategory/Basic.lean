/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Closure
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Projections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit two-fibre-product data in full subbicategories

The chosen apex, projections, and comparison cell for a cospan in a property-selected full subbicategory.
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

/-- The explicit two-fibre-product apex in the full subbicategory selected by `P`.

Its non-`Prop` data are exactly `BasedCategory.PseudoPullback F.hom G.hom`; the class instance
adds only the proof that this chosen object still satisfies `P`. -/
@[stacks 02XQ "two-fibre-product apex in a full subbicategory"]
def apex (F : X ⟶ S) (G : Y ⟶ S) : P.FullSubbicategory :=
  ⟨PseudoPullback F.hom G.hom,
    BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder.pseudoPullback_mem
      X.property Y.property S.property F.hom G.hom⟩

/-- Forgetting the selected-object witness from the explicit apex recovers the underlying
based pseudo-pullback. -/
@[simp]
theorem apex.obj (F : X ⟶ S) (G : Y ⟶ S) :
    (apex F G).1 = PseudoPullback F.hom G.hom := sorry

/-- Shared notation for the explicit two-fibre-product apex. The ambient full subbicategory
determines the object property, so the same notation applies uniformly to categories fibred in
groupoids, sets, setoids, and every later property closed under the chosen construction. -/
scoped[CategoryTheory.TwoFibreProduct] notation:max F:max " ⊡₂ " G:max => apex F G

/-- The first projection from the explicit two-fibre-product apex. -/
@[stacks 02XQ "left projection of a full-subbicategory two-fibre product"]
def fst (F : X ⟶ S) (G : Y ⟶ S) : apex F G ⟶ X :=
  Bicategory.InducedBicategory.mkHom
    (BasedCategory.PseudoPullback.fst F.hom G.hom)

/-- Forgetting the full-subbicategory first projection recovers the explicit based
pseudo-pullback projection. -/
@[simp]
theorem fst.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (fst F G).hom = BasedCategory.PseudoPullback.fst F.hom G.hom := sorry

/-- The second projection from the explicit two-fibre-product apex. -/
@[stacks 02XQ "right projection of a full-subbicategory two-fibre product"]
def snd (F : X ⟶ S) (G : Y ⟶ S) : apex F G ⟶ Y :=
  Bicategory.InducedBicategory.mkHom
    (BasedCategory.PseudoPullback.snd F.hom G.hom)

/-- Forgetting the full-subbicategory second projection recovers the explicit based
pseudo-pullback projection. -/
@[simp]
theorem snd.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (snd F G).hom = BasedCategory.PseudoPullback.snd F.hom G.hom := sorry

/-- The canonical invertible comparison between the two composites from the explicit
two-fibre-product apex to the cospan base. -/
@[stacks 02XQ "comparison isomorphism of a full-subbicategory two-fibre product"]
noncomputable def comparisonIso (F : X ⟶ S) (G : Y ⟶ S) :
    fst F G ≫ F ≅ snd F G ≫ G :=
  Bicategory.InducedBicategory.isoMk
    (BasedCategory.PseudoPullback.comparisonIso F.hom G.hom)

/-- Forgetting the forward full-subbicategory comparison cell recovers the explicit based
pseudo-pullback comparison. -/
@[simp]
theorem comparisonIso.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (comparisonIso F G).hom.hom =
      (BasedCategory.PseudoPullback.comparisonIso F.hom G.hom).hom := sorry

/-- Forgetting the inverse full-subbicategory comparison cell recovers the inverse explicit
based pseudo-pullback comparison. -/
@[simp]
theorem comparisonIso.inv (F : X ⟶ S) (G : Y ⟶ S) :
    (comparisonIso F G).inv.hom =
      (BasedCategory.PseudoPullback.comparisonIso F.hom G.hom).inv := sorry

end TwoFibreProduct

end CategoryTheory
