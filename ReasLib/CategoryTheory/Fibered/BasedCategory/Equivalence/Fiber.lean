/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Fiber
public import Mathlib.CategoryTheory.Groupoid

/-!
# Fiberwise consequences of based equivalences

This module turns an equivalence over the base into equivalences of total categories and standard
fibers, and transports fiberwise groupoid structure.
-/

@[expose] public section

namespace CategoryTheory

open BasedCategory
open BasedFunctor
open BasedNatTrans
open Functor.IsHomLift
open scoped Bicategory

universe u v uS uX uY vS vX vY

variable {C : Type u} [Category.{v} C]

namespace BasedFunctor

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- Forgetting the base data, an equivalence over the base is an equivalence of the underlying
categories. -/
@[instance]
theorem toFunctor.isEquivalence (F : X ⥤ᵇ Y) [F.IsEquivalence] :
    F.toFunctor.IsEquivalence := sorry
/- Proof strategy: select `F.asQuasiInverse`; forget the based unit and counit isomorphisms with
`BasedNatTrans.forgetful`, then apply `Functor.IsEquivalence.mk'` to the underlying inverse
functor. This uses only the fields of the encapsulated `QuasiInverse`, never its choice term. -/

/-- An equivalence over the base category induces an equivalence on every standard fiber. -/
@[instance]
theorem fiberFunctor.isEquivalence (F : X ⥤ᵇ Y) [F.IsEquivalence] (U : C) :
    (F.fiberFunctor U).IsEquivalence := sorry
/- Proof strategy: choose `e := F.asQuasiInverse` and first use
`toFunctor.isEquivalence F`. For the induced fiber functor, prove faithfulness by
`Functor.Fiber.hom_ext` and injectivity of `F.toFunctor.map`; prove fullness by taking an
underlying preimage and transporting its hom-lift condition with `F.isHomLift_iff`; prove
essential surjectivity using the components of `e.counitIso` as mutually inverse fiber morphisms.
Finally induce the inverse fiber functor from `e.inverse` and lift `e.unitIso` and `e.counitIso`
componentwise with `Functor.Fiber.homMk`; their naturality and inverse laws descend by fiber hom
extensionality. This records the former constructive proof without making the data owner opaque. -/

/-- An equivalence over the base transports the groupoid structure on each fiber forward along
the induced fiber equivalence. -/
theorem fiberIsGroupoid
    (F : X ⥤ᵇ Y) [F.IsEquivalence] (U : C) [IsGroupoid (X.p.Fiber U)] :
    IsGroupoid (Y.p.Fiber U) := sorry
/- Proof strategy: install `fiberFunctor.isEquivalence F U`, pass to its canonical
`asEquivalence.inverse`, and use `isGroupoid_of_reflects_iso` to transport the source-fiber
groupoid structure to the target fiber. -/

end BasedFunctor

end CategoryTheory
