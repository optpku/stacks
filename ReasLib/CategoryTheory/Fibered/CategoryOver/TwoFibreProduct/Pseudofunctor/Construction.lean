/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.TwoFibreProduct.Map.Computations
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Pseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-fibre-product pseudofunctor for fibred categories

This leaf owns the specialization of the generic locally induced two-fibre-product
pseudofunctor to fibred categories over a fixed base.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.TwoFibreProduct

/-- The explicit two-fibre-product construction as a pseudofunctor from bundled cospans of
fibred categories over `C` to fibred categories over `C`. -/
@[stacks 02XQ "two-fibre-product pseudofunctor of fibred categories"]
noncomputable def pseudofunctor :
    Bicategory.Cospan
        (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C) ⥤ᵖ
      FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C :=
  LocallyInduced.TwoFibreProduct.pseudofunctor
    (BasedCategory.isFibered C) (FiberedCategoryOver.homProperty C)

end FiberedCategoryOver.TwoFibreProduct

end CategoryTheory
