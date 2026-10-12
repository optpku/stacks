/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pro.Sequential.CommonRefinement

/-!
# Composition of sequential pro-morphism classes

Common-refinement classes of monotone sequential representatives carry canonical identity and
composition operations.  This is the proof-independent presentation layer for constructions that
must descend from representatives before the comparison with actual `Pro` morphisms is upgraded
to an equivalence.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.Pro.SequentialHom

variable {C : Type u} [Category.{v} C]
variable {X Y Z : ℕᵒᵖ ⥤ C}

namespace Equivalent

/-- Composition respects common-refinement equivalence in both variables. -/
theorem comp :
    ∀ {r r' : Pro.SequentialHom X Y}, r ≈ r' →
      ∀ {s s' : Pro.SequentialHom Y Z}, s ≈ s' →
        Pro.SequentialHom.comp r s ≈ Pro.SequentialHom.comp r' s' := sorry

end Equivalent

namespace Quotient

/-- The common-refinement class of the identity sequential representative. -/
def id (X : ℕᵒᵖ ⥤ C) : Pro.SequentialHom.Quotient (X := X) (Y := X) :=
  _root_.Quotient.mk (setoid (X := X) (Y := X)) (Pro.SequentialHom.id X)

/-- Composition of common-refinement classes, induced by composition of representatives. -/
def comp (q : Pro.SequentialHom.Quotient (X := X) (Y := Y))
    (r : Pro.SequentialHom.Quotient (X := Y) (Y := Z)) :
    Pro.SequentialHom.Quotient (X := X) (Y := Z) :=
  _root_.Quotient.map₂
    (fun (q : Pro.SequentialHom X Y) (r : Pro.SequentialHom Y Z) ↦
      Pro.SequentialHom.comp q r)
    (fun _ _ hq _ _ hr ↦ Equivalent.comp hq hr) q r

/-- The class of a composite representative is the composite of its two classes. -/
@[simp]
theorem comp_mk (r : Pro.SequentialHom X Y) (s : Pro.SequentialHom Y Z) :
    comp (_root_.Quotient.mk (setoid (X := X) (Y := Y)) r)
      (_root_.Quotient.mk (setoid (X := Y) (Y := Z)) s) =
        _root_.Quotient.mk (setoid (X := X) (Y := Z)) (Pro.SequentialHom.comp r s) := sorry

/-- The identity class is sent to the identity pro-morphism. -/
@[simp]
theorem quotientToHom_id (X : ℕᵒᵖ ⥤ C) :
    quotientToHom (id X) = 𝟙 ((Pro.lim (C := C) ℕᵒᵖ).obj X) := sorry

/-- The comparison with actual pro-morphisms preserves composition. -/
@[simp]
theorem quotientToHom_comp
    (q : Pro.SequentialHom.Quotient (X := X) (Y := Y))
    (r : Pro.SequentialHom.Quotient (X := Y) (Y := Z)) :
    quotientToHom (comp q r) = quotientToHom q ≫ quotientToHom r := sorry

end Quotient

end CategoryTheory.Pro.SequentialHom
