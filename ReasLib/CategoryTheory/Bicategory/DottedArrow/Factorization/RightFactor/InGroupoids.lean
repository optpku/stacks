/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Groupoid
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Factorization.RightFactor.Basic
public import ReasLib.CategoryTheory.Functor.MappingPath.InGroupoids

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace DottedArrow

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.IsLocallyGroupoid B]
variable {T X Y Z : B} {z : T ⟶ Z} {f : X ⟶ Y} {g : Y ⟶ Z}
variable (sq : Bicategory.PseudoPullbackCone z (f ≫ g))

namespace Factorization

/-- The canonical projection from the mapping-path factorization of dotted arrows is fibred in
groupoids whenever the ambient bicategory is locally groupoidal. -/
@[stacks 0H1B "(2) fibred projection"]
instance projectionInGroupoids :
    Functor.IsFibered.InGroupoids (projection sq) := sorry

end Factorization

end DottedArrow

end CategoryTheory
