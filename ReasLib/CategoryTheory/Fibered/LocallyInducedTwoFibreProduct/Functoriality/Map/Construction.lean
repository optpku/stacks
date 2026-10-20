module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Functoriality.Forget
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of locally induced two-fibre products

A selected cospan transformation induces the explicit pseudo-pullback map, bundled with the
hom-property detected by the two projections.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory BasedFunctor Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace LocallyInduced.TwoFibreProduct

variable {P : ObjectProperty (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable {Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1)}
variable [Q.IsMultiplicative]
variable [BasedCategory.PseudoPullback.HomProperty.IsClosedUnder Q]
variable [projections : Projections.Has (P := P) (Q := Q)]
variable [isoClosed : Q.IsClosedUnderIsomorphisms]
variable [detected : Projections.IsDetected (P := P) (Q := Q)]
variable {X₁ Y₁ S₁ X₂ Y₂ S₂ : Bicategory.LocallyInducedBicategory
  (BasedCategory.{max v vB, max w (max u (max v vB))} C)
  (fun X : P.FullSubbicategory ↦ X.1) Q}
variable {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
variable {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}

omit detected in
include projections isoClosed in
/-- The ambient map of a selected cospan transformation has a selected composite with the
first explicit pseudo-pullback projection. -/
theorem map.fst_mem
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    Q (apex F₁ G₁) X₂
      (BasedCategory.PseudoPullback.map (CospanTransform.forget ψ) ≫
        BasedCategory.PseudoPullback.fst F₂.obj G₂.obj) := sorry

omit detected in
include projections isoClosed in
/-- The ambient map of a selected cospan transformation has a selected composite with the
second explicit pseudo-pullback projection. -/
theorem map.snd_mem
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    Q (apex F₁ G₁) Y₂
      (BasedCategory.PseudoPullback.map (CospanTransform.forget ψ) ≫
        BasedCategory.PseudoPullback.snd F₂.obj G₂.obj) := sorry

include projections isoClosed detected in
/-- The componentwise ambient map of pseudo-pullbacks satisfies the selected hom property. -/
theorem map.mem
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    Q (apex F₁ G₁) (apex F₂ G₂)
      (BasedCategory.PseudoPullback.map (CospanTransform.forget ψ)) := sorry

/-- A transformation of selected cospans induces the componentwise map of their explicit
two-fibre products. -/
@[stacks 0040 "map of locally induced two-fibre-products from a cospan transformation"]
noncomputable def map
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    apex F₁ G₁ ⟶ apex F₂ G₂ :=
  Bicategory.LocallyInducedBicategory.mkHom
    (BasedCategory.PseudoPullback.map (CospanTransform.forget ψ)) (map.mem ψ)

/-- Forgetting an induced selected map recovers the explicit based pseudo-pullback map. -/
@[simp]
theorem map.obj
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    (map ψ).obj =
      BasedCategory.PseudoPullback.map (CospanTransform.forget ψ) := sorry

end LocallyInduced.TwoFibreProduct

end CategoryTheory
