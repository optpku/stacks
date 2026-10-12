/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace CategoryTheory.FiberedCategoryOver.Groupoids

/-- Lemma 94.6.2: let `S` be a scheme. Consider a 2-commutative square of 1-morphisms
of categories fibred in groupoids over `Over S`, with horizontal arrows equivalences
`eX : X' ≌ X` and `eY : Y' ≌ Y` and vertical arrows `f : X ⟶ Y` and `f' : X' ⟶ Y'`.
Then `f` is a representable 1-morphism if and only if `f'` is a representable
1-morphism. -/
@[stacks 0456]
theorem relativelyRepresentable.iff_of_equivalence
    {S : Scheme.{u}}
    {X' X Y' Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (eX : X' ≌ X) (eY : Y' ≌ Y) (η : eX.hom ≫ f ≅ f' ≫ eY.hom) :
    relativelyRepresentable f ↔ relativelyRepresentable f' := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids
