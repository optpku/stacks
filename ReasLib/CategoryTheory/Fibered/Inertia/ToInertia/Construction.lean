/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Based.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction from relative inertia to absolute inertia

This leaf owns the canonical based functor which forgets the relative-kernel
condition. Its object and morphism formulas are exposed separately by
`ToInertia.Computations`.
-/

@[expose] public section

universe u v u₁ v₁ u₁' v₁'

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans

variable {C : Type u} [Category.{v} C]

section ToInertia

variable {X : BasedCategory.{v₁, u₁} C} {Y : BasedCategory.{v₁', u₁'} C}

/-- Forgetting the relative kernel condition commutes with projection to the base. -/
@[stacks 04Z5 "relative-to-absolute inertia projection computation"]
theorem RelativeInertia.toInertia.comm (F : X ⥤ᵇ Y) :
    CategoryTheory.RelativeInertia.map (𝟭 X.obj) Y.p F.projectionIso ⋙
        (inertia X).p =
      (relativeInertia F).p := sorry

/- Proof strategy: unfold the relative- and absolute-inertia projections; both sides map an
inertia object and morphism through X.p. -/

/-- Forget the relative kernel condition, mapping based relative inertia to absolute inertia. -/
@[stacks 04Z5 "relative-to-absolute inertia comparison"]
def RelativeInertia.toInertia (F : X ⥤ᵇ Y) :
    relativeInertia F ⥤ᵇ inertia X where
  toFunctor := CategoryTheory.RelativeInertia.map (𝟭 X.obj) Y.p F.projectionIso
  w := RelativeInertia.toInertia.comm F

end ToInertia

end BasedCategory
end CategoryTheory
