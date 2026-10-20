/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable

/-!
# Two-fibre products representable by algebraic spaces

Base change of a morphism representable by algebraic spaces along a groupoid
fibration representable by an algebraic space has representable apex.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- If `f : X ⟶ Y` is representable by algebraic spaces and `Z` is representable
by an algebraic space over `S`, then the two-fibre product of `g : Z ⟶ Y` and
`f` is representable by an algebraic space over `S`. -/
@[stacks 0300]
theorem IsRepresentableByAlgebraicSpace.twoFibreProduct
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (hZ : IsRepresentableByAlgebraicSpace Z) :
    IsRepresentableByAlgebraicSpace
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} g f) := sorry

end AlgebraicGeometry
