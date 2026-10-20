/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.TwoFibreProduct.Isomorphism.Collapse.Unit

/-!
# The collapse counit

This leaf constructs the explicit counit from deterministic reconstruction followed by collapse.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Opposite CategoryOfElements
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct.Isomorphism

variable (X : FiberedCategoryOver C) {U : C} (x y : X.p.Fiber U)

namespace collapse
namespace counitComponent

/-- The reconstructed collapsed element lies over the same base object as the original element. -/
@[stacks 04SI "counit base equality readout"]
theorem baseEq (q : total X x y) :
    q.unop.1 = (((inverse X x y) ⋙ (collapse X x y)).obj q).unop.1 := sorry

/-- The base isomorphism underlying the deterministic collapse counit. -/
@[stacks 04SI "counit base comparison"]
noncomputable def base (q : total X x y) :
    q.unop.1 ≅ (((inverse X x y) ⋙ (collapse X x y)).obj q).unop.1 :=
  Iso.refl _
/- Data audit: the inverse and category-of-elements section both retain the displayed slice object
definitionally. The equality theorem above is a readout and is not used to construct this base
isomorphism. -/

/-- The reconstructed and original elements have the same section after base transport. -/
@[stacks 04SI "counit section property"]
theorem property (q : total X x y) :
    (presheafULift X x y).map (base X x y q).hom q.unop.2 =
      (((inverse X x y) ⋙ (collapse X x y)).obj q).unop.2 := sorry

end counitComponent

/-- Collapsing the deterministic reconstruction of a Grothendieck element is explicitly
isomorphic to that element over the identity slice object. -/
@[stacks 04SI "collapse counit component"]
noncomputable def counitComponent (q : total X x y) :
    ((inverse X x y) ⋙ (collapse X x y)).obj q ≅ q :=
  Iso.op <| CategoryOfElements.isoMk q.unop
    (((inverse X x y) ⋙ (collapse X x y)).obj q).unop
    (counitComponent.base X x y q) (counitComponent.property X x y q)

namespace counitComponent.hom

/-- The base map underlying the forward counit component. -/
@[simp, stacks 04SI "counit forward base readout"]
theorem val (q : total X x y) :
    (counitComponent X x y q).hom.unop.val =
      (counitComponent.base X x y q).hom := sorry

end counitComponent.hom

namespace counitComponent.inv

/-- The base map underlying the inverse counit component. -/
@[simp, stacks 04SI "counit inverse base readout"]
theorem val (q : total X x y) :
    (counitComponent X x y q).inv.unop.val =
      (counitComponent.base X x y q).inv := sorry

end counitComponent.inv

namespace counitComponent

/-- The explicit collapse counit components are natural in Grothendieck morphisms. -/
@[stacks 04SI "counit component naturality"]
theorem naturality {q r : total X x y} (f : q ⟶ r) :
    ((inverse X x y) ⋙ (collapse X x y)).map f ≫
        (collapse.counitComponent X x y r).hom =
      (collapse.counitComponent X x y q).hom ≫ f := sorry

/-- Every collapse counit component is vertical over the identity slice arrow. -/
@[stacks 04SI "counit component verticality"]
theorem isHomLift (q : total X x y) :
    (fibration X x y).p.IsHomLift
      (𝟙 ((fibration X x y).p.obj q))
      (collapse.counitComponent X x y q).hom := sorry

end counitComponent

/-- The explicit counit from deterministic reconstruction followed by collapse to the identity on
the canonical Grothendieck owner. -/
@[stacks 04SI "collapse counit isomorphism"]
noncomputable def counitIso :
    inverse X x y ⋙ collapse X x y ≅
      𝟭 (fibration X x y).toBasedCategory :=
  BasedNatIso.ofComponents (counitComponent X x y)
    (counitComponent.naturality X x y) (counitComponent.isHomLift X x y)

namespace counitIso.hom

/-- The forward component of the packaged collapse counit. -/
@[simp, stacks 04SI "counit isomorphism forward readout"]
theorem app (q : total X x y) :
    (counitIso X x y).hom.app q = (counitComponent X x y q).hom := sorry

end counitIso.hom

namespace counitIso.inv

/-- The inverse component of the packaged collapse counit. -/
@[simp, stacks 04SI "counit isomorphism inverse readout"]
theorem app (q : total X x y) :
    (counitIso X x y).inv.app q = (counitComponent X x y q).inv := sorry

end counitIso.inv
end collapse
end FiberedCategoryOver.TwoFibreProduct.Isomorphism
end CategoryTheory
