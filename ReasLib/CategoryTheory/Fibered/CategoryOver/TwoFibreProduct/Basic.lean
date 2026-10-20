module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Fibered.Closure
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Bilimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-fibre products of fibred categories over a base

This leaf owns the application-facing carrier, projections, comparison isomorphism, and
pseudo-pullback cone.  The generic `LocallyInduced.TwoFibreProduct` construction remains the
underlying data owner.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct

variable {X Y S :
  FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C}

/-- The explicit two-fibre-product carrier of a cospan of fibred categories over `C`. -/
@[stacks 02XQ "two-fibre product carrier"]
abbrev apex
    (F : X ⟶ S) (G : Y ⟶ S) :
    FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C :=
  LocallyInduced.TwoFibreProduct.apex
    (P := BasedCategory.isFibered C)
    (Q := FiberedCategoryOver.homProperty C) F G

/-- The first projection from the explicit two-fibre-product carrier. -/
@[stacks 02XQ "left projection"]
abbrev fst (F : X ⟶ S) (G : Y ⟶ S) :
    apex F G ⟶ X :=
  LocallyInduced.TwoFibreProduct.fst
    (P := BasedCategory.isFibered C)
    (Q := FiberedCategoryOver.homProperty C) F G

/-- The second projection from the explicit two-fibre-product carrier. -/
@[stacks 02XQ "right projection"]
abbrev snd (F : X ⟶ S) (G : Y ⟶ S) :
    apex F G ⟶ Y :=
  LocallyInduced.TwoFibreProduct.snd
    (P := BasedCategory.isFibered C)
    (Q := FiberedCategoryOver.homProperty C) F G

/-- The canonical invertible comparison between the two projections followed by the cospan
legs. -/
@[stacks 02XQ "comparison isomorphism"]
noncomputable abbrev comparisonIso (F : X ⟶ S) (G : Y ⟶ S) :
    fst F G ≫ F ≅ snd F G ≫ G :=
  LocallyInduced.TwoFibreProduct.comparisonIso
    (P := BasedCategory.isFibered C)
    (Q := FiberedCategoryOver.homProperty C) F G

/-- The canonical pseudo-pullback cone of a cospan of fibred categories. -/
@[stacks 02XQ "pseudo-pullback cone"]
noncomputable abbrev cone (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.PseudoPullbackCone F G :=
  LocallyInduced.TwoFibreProduct.cone
    (P := BasedCategory.isFibered C)
    (Q := FiberedCategoryOver.homProperty C) F G

/-- The application-facing cone has the explicit two-fibre-product carrier as its apex. -/
@[simp]
theorem cone.pt (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).pt = apex F G := sorry

/-- The first leg of the application-facing cone is the first selected projection. -/
@[simp]
theorem cone.fst (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).fst = fst F G := sorry

/-- The second leg of the application-facing cone is the second selected projection. -/
@[simp]
theorem cone.snd (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).snd = snd F G := sorry

/-- The structural cell of the application-facing cone is the selected comparison
isomorphism. -/
@[simp]
theorem cone.iso (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).iso = comparisonIso F G := sorry

end FiberedCategoryOver.TwoFibreProduct

end CategoryTheory
