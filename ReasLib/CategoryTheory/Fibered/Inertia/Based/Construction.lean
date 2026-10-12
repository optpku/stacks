/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Based.Verticality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Based relative- and absolute-inertia constructions

This leaf owns the based relative-inertia and absolute-inertia objects together
with their canonical forgetful based functors. Projection and underlying-functor
readouts live in `Based.Computations`.
-/

@[expose] public section

universe u v uX vX uY vY

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}

/-- Relative inertia of a based functor, packaged as a category over the same base. -/
@[stacks 034I "relative inertia over a base"]
def relativeInertia (F : X ⥤ᵇ Y) : BasedCategory.{vX, max uX vX} C :=
  BasedCategory.ofFunctor
    (CategoryTheory.RelativeInertia.projection F.toFunctor X.p)

/-- Definition 4.34.2 (2) (Stacks 034I): absolute inertia of a category over `C`, obtained from
its structure functor to `C`. -/
@[stacks 034I "absolute inertia over a base"]
def inertia (X : BasedCategory.{vX, uX} C) : BasedCategory.{vX, max uX vX} C :=
  relativeInertia X.toBase

/-- The neutral relative-inertia forgetful functor commutes with projection to `C`. -/
theorem RelativeInertia.forget.comm (F : X ⥤ᵇ Y) :
    CategoryTheory.RelativeInertia.forget F.toFunctor ⋙ X.p =
      (relativeInertia F).p := sorry
/- Proof strategy: both sides map an inertia object and morphism through the source projection. -/

/-- Forget the automorphism from based relative inertia, retaining its source object. -/
@[stacks 042H "(1) relative-inertia structure map"]
def RelativeInertia.forget (F : X ⥤ᵇ Y) : relativeInertia F ⥤ᵇ X where
  toFunctor := CategoryTheory.RelativeInertia.forget F.toFunctor
  w := RelativeInertia.forget.comm F

/-- Forget the automorphism from based absolute inertia. -/
@[stacks 042H "(2) absolute-inertia structure map"]
def Inertia.forget (X : BasedCategory.{vX, uX} C) : inertia X ⥤ᵇ X :=
  RelativeInertia.forget X.toBase

end BasedCategory
end CategoryTheory
