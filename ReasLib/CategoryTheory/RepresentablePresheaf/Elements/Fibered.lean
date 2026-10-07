module

public import ReasLib.CategoryTheory.RepresentablePresheaf.Elements.OverEquivalence
public import ReasLib.CategoryTheory.Fibered.InSets.Hom.OneCell
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.FullSubbicategory
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Elements
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Slice
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0178

# Representable elements as a fibred slice category

The representable-elements equivalence is bundled over the base as an equivalence of categories
fibred in sets. The underlying ordinary equivalence and its computations live in the lighter
`RepresentablePresheaf.Elements.OverEquivalence` leaf.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Opposite CategoryOfElements
open scoped Bicategory RepresentablePresheaf

variable {C : Type u} [Category.{v} C]

namespace RepresentablePresheaf.Elements

/-- The canonical representable category-of-elements comparison, bundled as a morphism of
categories fibred in sets over `C`. -/
@[stacks 0178 "representable category-of-elements comparison over the base"]
noncomputable def comparison (X : C) :
    FiberedCategoryOver.Sets.ofFunctor ((π h[X]).leftOp) ⟶
      FiberedCategoryOver.Sets.ofFunctor (Over.forget X) :=
  FiberedCategoryOver.Sets.ofBasedFunctor
    (BasedFunctor.ofFunctor (overEquivalence X).functor
      (overEquivalence.functor.comm X))

namespace comparison

/-- Forgetting the fibred-in-sets packaging, the comparison is the forward functor of the
ordinary representable-elements equivalence. -/
@[simp, stacks 0178 "underlying representable-elements comparison functor"]
theorem toFunctor (X : C) :
    FiberedCategoryOver.Sets.toFunctor (comparison X) =
      (overEquivalence X).functor := sorry

/-- The bundled comparison sends the element represented by `f` to the slice object
`Over.mk f`. -/
@[simp, stacks 0178 "representable-elements comparison object formula"]
theorem obj
    {X U : C} (f : U ⟶ X) :
    (FiberedCategoryOver.Sets.toFunctor
      (comparison X)).obj
        (op (h[X].elementsMk (op U) f)) =
      Over.mk f := sorry

/-- Forgetting the fibred-in-sets packaging, the comparison map is the morphism map of the
representable-elements equivalence. -/
@[simp, stacks 0178 "representable-elements comparison map formula"]
theorem map (X : C) {a b : h[X].Elementsᵒᵖ} (φ : a ⟶ b) :
    (FiberedCategoryOver.Sets.toFunctor (comparison X)).map φ =
      (overEquivalence X).functor.map φ := sorry

/-- The underlying object selected by the bundled comparison is the domain of the represented
element. -/
@[simp, stacks 0178 "representable-elements comparison domain formula"]
theorem obj.left (X : C) (a : h[X].Elementsᵒᵖ) :
    ((FiberedCategoryOver.Sets.toFunctor (comparison X)).obj a).left =
      (unop a).fst.unop := sorry

/-- The slice-arrow component of the bundled comparison is the underlying arrow of the
opposite category-of-elements morphism. -/
@[simp, stacks 0178 "representable-elements comparison arrow formula"]
theorem map.left {X : C} {a b : h[X].Elementsᵒᵖ} (φ : a ⟶ b) :
    ((FiberedCategoryOver.Sets.toFunctor (comparison X)).map φ).left =
      eqToHom (obj.left X a) ≫ φ.unop.val.unop ≫
        eqToHom (obj.left X b).symm := sorry

/-- The bundled comparison commutes strictly with the projections to `C`. -/
@[simp, stacks 0178 "representable-elements comparison base projection"]
theorem comm (X : C) :
    FiberedCategoryOver.Sets.toFunctor (comparison X) ⋙ Over.forget X =
      (π h[X]).leftOp := sorry

/-- The explicit inverse to the representable-elements comparison over `C`.  Its underlying
functor is the inverse of `overEquivalence X`; only its strict base equation is proof-valued. -/
@[stacks 0178 "inverse representable category-of-elements comparison over the base"]
noncomputable def inverse (X : C) :
    FiberedCategoryOver.Sets.ofFunctor (Over.forget X) ⟶
      FiberedCategoryOver.Sets.ofFunctor ((π h[X]).leftOp) :=
  FiberedCategoryOver.Sets.ofBasedFunctor
    (BasedFunctor.ofFunctor (overEquivalence X).inverse
      (overEquivalence.inverse.comm X))

namespace inverse

/-- Forgetting the fibred-in-sets packaging, the explicit comparison inverse is the inverse
functor of the ordinary representable-elements equivalence. -/
@[simp, stacks 0178 "underlying inverse representable-elements comparison functor"]
theorem toFunctor (X : C) :
    FiberedCategoryOver.Sets.toFunctor (inverse X) =
      (overEquivalence X).inverse := sorry

end inverse

namespace quasiInverse

/-- The unit of the ordinary representable-elements equivalence is vertical over `C`. -/
@[stacks 0178 "representable-elements comparison unit over the base"]
theorem unitIsHomLift (X : C) (a : h[X].Elementsᵒᵖ) :
    ((π h[X]).leftOp).IsHomLift
      (𝟙 (((π h[X]).leftOp).obj a))
      ((overEquivalence X).unitIso.hom.app a) := sorry

/-- The counit of the ordinary representable-elements equivalence is vertical over `C`. -/
@[stacks 0178 "representable-elements comparison counit over the base"]
theorem counitIsHomLift (X : C) (a : Over X) :
    (Over.forget X).IsHomLift
      (𝟙 ((Over.forget X).obj a))
      ((overEquivalence X).counitIso.hom.app a) := sorry

end quasiInverse

/-- Explicit based quasi-inverse data for `comparison X`.  The inverse functor and the
underlying unit and counit are inherited from `overEquivalence X`; no witness is selected from
the proposition `comparison.isEquivalence`. -/
@[stacks 0178 "explicit representable-elements quasi-inverse over the base"]
noncomputable def quasiInverse (X : C) :
    BasedFunctor.QuasiInverse
      (FiberedCategoryOver.Sets.toBasedFunctor (comparison X)) where
  inverse := FiberedCategoryOver.Sets.toBasedFunctor (inverse X)
  unitIso := BasedNatIso.mkNatIso (overEquivalence X).unitIso
    (quasiInverse.unitIsHomLift X)
  counitIso := BasedNatIso.mkNatIso (overEquivalence X).counitIso
    (quasiInverse.counitIsHomLift X)

namespace quasiInverse

/-- The inverse field of the explicit quasi-inverse is the underlying based functor of the
explicit comparison inverse. -/
@[simp, stacks 0178 "representable-elements quasi-inverse functor formula"]
theorem inverse (X : C) :
    (quasiInverse X).inverse =
      FiberedCategoryOver.Sets.toBasedFunctor (comparison.inverse X) := sorry

/-- The underlying forward unit transformation of the explicit quasi-inverse is the forward
unit transformation of the ordinary representable-elements equivalence. -/
@[simp, stacks 0178 "representable-elements quasi-inverse unit formula"]
theorem unitIso.hom.toNatTrans (X : C) :
    (quasiInverse X).unitIso.hom.toNatTrans =
      (overEquivalence X).unitIso.hom := sorry

/-- The underlying inverse unit transformation of the explicit quasi-inverse is the inverse
unit transformation of the ordinary representable-elements equivalence. -/
@[simp, stacks 0178 "representable-elements quasi-inverse inverse-unit formula"]
theorem unitIso.inv.toNatTrans (X : C) :
    (quasiInverse X).unitIso.inv.toNatTrans =
      (overEquivalence X).unitIso.inv := sorry

/-- The underlying forward counit transformation of the explicit quasi-inverse is the forward
counit transformation of the ordinary representable-elements equivalence. -/
@[simp, stacks 0178 "representable-elements quasi-inverse counit formula"]
theorem counitIso.hom.toNatTrans (X : C) :
    (quasiInverse X).counitIso.hom.toNatTrans =
      (overEquivalence X).counitIso.hom := sorry

/-- The underlying inverse counit transformation of the explicit quasi-inverse is the inverse
counit transformation of the ordinary representable-elements equivalence. -/
@[simp, stacks 0178 "representable-elements quasi-inverse inverse-counit formula"]
theorem counitIso.inv.toNatTrans (X : C) :
    (quasiInverse X).counitIso.inv.toNatTrans =
      (overEquivalence X).counitIso.inv := sorry

end quasiInverse

/-- The discrete fibration attached to `h[X]` is equivalent over `C` to the slice projection
`Over.forget X`.  The corresponding explicit witness is `quasiInverse X`. -/
@[stacks 0178 "representable category-of-elements comparison is an equivalence"]
instance isEquivalence (X : C) :
    BasedFunctor.IsEquivalence
      (FiberedCategoryOver.Sets.toBasedFunctor
        (comparison X)) := sorry

end comparison

/-- The representable category of elements and the corresponding slice are canonically
equivalent as categories fibred in sets over `C`. This is the fixed-owner lift of
`overEquivalence`. -/
@[stacks 0178 "representable category of elements as a fibred slice category"]
noncomputable def fiberedEquivalence (X : C) :
    FiberedCategoryOver.Sets.ofFunctor ((π h[X]).leftOp) ≌
      FiberedCategoryOver.Sets.ofFunctor (Over.forget X) :=
  ObjectProperty.FullSubbicategory.equivalenceOfQuasiInverse
    (comparison X) (comparison.quasiInverse X)

namespace fiberedEquivalence

/-- The forward morphism of the representable-elements equivalence over the base is the
canonical bundled comparison. -/
@[simp, stacks 0178 "fibred representable-elements equivalence forward morphism"]
theorem hom (X : C) :
    (fiberedEquivalence X).hom = comparison X := sorry

/-- The inverse morphism of the representable-elements equivalence is the lift of the selected
explicit inverse based functor. -/
@[simp, stacks 0178 "fibred representable-elements equivalence inverse morphism"]
theorem inv (X : C) :
    (fiberedEquivalence X).inv = comparison.inverse X := sorry

/-! The unit computations of the representable-elements equivalence. -/
namespace unit

/-- The underlying based forward unit cell of the representable-elements equivalence is the
canonical adjustment of the selected based unit against the selected based counit. -/
@[simp, stacks 0178 "fibred representable-elements equivalence unit"]
theorem hom (X : C) :
    (fiberedEquivalence X).unit.hom.hom =
      (Bicategory.Equivalence.adjointifyUnit
        (comparison.quasiInverse X).unitIso
        (comparison.quasiInverse X).counitIso).hom := sorry

/-- The underlying based inverse unit cell of the representable-elements equivalence is the
inverse canonical adjustment of the selected based unit. -/
@[simp, stacks 0178 "fibred representable-elements equivalence inverse unit"]
theorem inv (X : C) :
    (fiberedEquivalence X).unit.inv.hom =
      (Bicategory.Equivalence.adjointifyUnit
        (comparison.quasiInverse X).unitIso
        (comparison.quasiInverse X).counitIso).inv := sorry

end unit

/-! The counit computations of the representable-elements equivalence. -/
namespace counit

/-- The underlying based forward counit cell of the representable-elements equivalence is the
selected based counit. -/
@[simp, stacks 0178 "fibred representable-elements equivalence counit"]
theorem hom (X : C) :
    (fiberedEquivalence X).counit.hom.hom =
      (comparison.quasiInverse X).counitIso.hom := sorry

/-- The underlying based inverse counit cell of the representable-elements equivalence is the
inverse selected based counit. -/
@[simp, stacks 0178 "fibred representable-elements equivalence inverse counit"]
theorem inv (X : C) :
    (fiberedEquivalence X).counit.inv.hom =
      (comparison.quasiInverse X).counitIso.inv := sorry

/-- The forward counit component of the fibred representable-elements equivalence is the
forward counit component of the ordinary equivalence. -/
@[simp, stacks 0178 "fibred representable-elements forward counit component"]
theorem hom.app (X : C) (a : Over X) :
    (fiberedEquivalence X).counit.hom.hom.toNatTrans.app a =
      (overEquivalence X).counitIso.hom.app a := sorry

/-- The inverse counit component of the fibred representable-elements equivalence is the
inverse counit component of the ordinary equivalence. -/
@[simp, stacks 0178 "fibred representable-elements inverse counit component"]
theorem inv.app (X : C) (a : Over X) :
    (fiberedEquivalence X).counit.inv.hom.toNatTrans.app a =
      (overEquivalence X).counitIso.inv.app a := sorry

end counit
end fiberedEquivalence
end RepresentablePresheaf.Elements
end CategoryTheory
