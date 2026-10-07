module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Basic

/-!
# Universal lifts for colax costructured arrows

A universal colax costructured arrow represents the functor `a ↦ (K.obj a ⟶ X)` up to
equivalence. The chosen inverse of each represented comparison supplies universal source maps and
`2`-morphisms. This file owns that shape-independent data and hides the choice behind unit,
counit, comparison, and uniqueness isomorphisms.

Specialized presentations, such as conical bilimits and pseudo-pullbacks, should expose readable
facades over this API rather than choose a second family of inverse functors.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe wA vA uA wC vC uC

namespace CategoryTheory

open Bicategory

namespace Bicategory.ColaxCostructuredArrow.IsUniversal

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : A ⥤ᵖ C} {X : C}

/-- The chosen quasi-inverse to the comparison represented by a universal costructured arrow. -/
noncomputable def lift.functor (T : ColaxCostructuredArrow K X) [T.IsUniversal] (a : A) :
    (K.obj a ⟶ X) ⥤ (a ⟶ T.left) :=
  (T.comparison a).inv

/-- Comparing a chosen lift recovers the represented object, naturally in represented
`2`-morphisms. -/
noncomputable def lift.counitIso (T : ColaxCostructuredArrow K X) [T.IsUniversal] (a : A) :
    lift.functor T a ⋙ T.comparison a ≅ Functor.id (K.obj a ⟶ X) :=
  (T.comparison a).asEquivalence.counitIso

/-- Lifting a represented source map recovers that map, naturally in its `2`-morphisms. -/
noncomputable def lift.unitIso (T : ColaxCostructuredArrow K X) [T.IsUniversal] (a : A) :
    Functor.id (a ⟶ T.left) ≅ T.comparison a ⋙ lift.functor T a :=
  (T.comparison a).asEquivalence.unitIso

namespace lift.functor

/-- Applying comparison after the chosen inverse conjugates a represented `2`-morphism by the
counit isomorphism. -/
@[simp]
theorem comparison_map (T : ColaxCostructuredArrow K X) [T.IsUniversal]
    (a : A) {f g : K.obj a ⟶ X} (η : f ⟶ g) :
    (T.comparison a).map ((lift.functor T a).map η) =
      (lift.counitIso T a).hom.app f ≫ η ≫ (lift.counitIso T a).inv.app g := sorry

/-- Applying the chosen inverse after comparison conjugates a source `2`-morphism by the unit
isomorphism. -/
@[simp]
theorem map_comparison (T : ColaxCostructuredArrow K X) [T.IsUniversal]
    (a : A) {f g : a ⟶ T.left} (η : f ⟶ g) :
    (lift.functor T a).map ((T.comparison a).map η) =
      (lift.unitIso T a).inv.app f ≫ η ≫ (lift.unitIso T a).hom.app g := sorry

end lift.functor

/-- The chosen universal source map from a costructured arrow `S` to a universal
costructured arrow `T`. -/
noncomputable def lift (S T : ColaxCostructuredArrow K X) [T.IsUniversal] :
    S.left ⟶ T.left :=
  (lift.functor T S.left).obj S.hom

namespace lift.functor

/-- The chosen inverse sends the structural map of `S` to its universal source map into `T`. -/
@[simp]
theorem obj (S T : ColaxCostructuredArrow K X) [T.IsUniversal] :
    (lift.functor T S.left).obj S.hom = lift S T := sorry

end lift.functor

/-- Comparing the chosen universal source map recovers the structural map of its source
costructured arrow. -/
noncomputable def lift.comparisonIso (S T : ColaxCostructuredArrow K X) [T.IsUniversal] :
    (T.comparison S.left).obj (lift S T) ≅ S.hom :=
  (counitIso T S.left).app S.hom

/-- Any source map presenting `S` under the represented comparison is canonically isomorphic to
the chosen universal source map from `S` to `T`. -/
noncomputable def lift.uniqueIso (S T : ColaxCostructuredArrow K X) [T.IsUniversal]
    (f : S.left ⟶ T.left) (e : (T.comparison S.left).obj f ≅ S.hom) :
    f ≅ lift S T :=
  (T.comparison S.left).preimageIso (e ≪≫ (lift.comparisonIso S T).symm)

namespace lift.uniqueIso

/-- Comparison sends the forward cell of `lift.uniqueIso` to the supplied presentation followed
by the inverse chosen-lift comparison. -/
@[simp]
theorem map_hom (S T : ColaxCostructuredArrow K X) [T.IsUniversal]
    (f : S.left ⟶ T.left) (e : (T.comparison S.left).obj f ≅ S.hom) :
    (T.comparison S.left).map (lift.uniqueIso S T f e).hom =
      (e ≪≫ (lift.comparisonIso S T).symm).hom := sorry

/-- Comparison sends the inverse cell of `lift.uniqueIso` to the inverse of the supplied
presentation composite. -/
@[simp]
theorem map_inv (S T : ColaxCostructuredArrow K X) [T.IsUniversal]
    (f : S.left ⟶ T.left) (e : (T.comparison S.left).obj f ≅ S.hom) :
    (T.comparison S.left).map (lift.uniqueIso S T f e).inv =
      (e ≪≫ (lift.comparisonIso S T).symm).inv := sorry

end lift.uniqueIso

/- Data and axiom audit (mathlib 4.32):

The non-`Prop` payload is obtained only from the selected inverse of an equivalence and its
unit/counit/preimage API. The audit may inherit `sorryAx` from `Prop`-valued bicategory,
pseudofunctor, and comma coherence fields in the current statement-stage support layer; no
semantic datum in this file is itself supplied by `sorry`. -/

end Bicategory.ColaxCostructuredArrow.IsUniversal

end CategoryTheory
