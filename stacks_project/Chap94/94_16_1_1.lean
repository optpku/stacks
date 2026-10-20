/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.CanonicalHom
import StacksCheckRecall

/-!
# Canonical action of `f_can` on morphisms

The switched-comparison equation describes the fibrewise arrow rule used in
the construction of `f_can : [U/R] ⟶ X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/- 94.16.1.1: a fibrewise arrow `φ : a ⟶ b` is represented by the switched
triple `(b, a, α)`, with `α : f(b) ≅ f(a)`. The fibrewise arrow rule used in
the construction of `f_can` sends this triple to `α.inv : f(a) ⟶ f(b)`. -/
@[stacks 04TG] #check (AlgebraicGeometry.canonicalHom_eq_inv :
  ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
    {T : Over S} (a b : U.p.Fiber T)
    (α : (fiberFunctor f T).obj b ≅ (fiberFunctor f T).obj a),
    AlgebraicGeometry.canonicalHom f
      (AlgebraicGeometry.ofSwitchedComparison f a b α) = α.inv)

end AlgebraicGeometry
