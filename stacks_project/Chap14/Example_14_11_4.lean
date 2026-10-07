module

public import ReasLib.CategoryTheory.RepresentablePresheaf.Elements.Fibered
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import StacksCheckRecall

/-!
@stack 0178

# Source-facing recall for Example 14.11.4

The category of elements of a representable simplicial presheaf is identified with the
corresponding slice category, and simplicial Yoneda gives the resulting simplex formula.
-/

@[expose] public section

open CategoryTheory
open scoped Bicategory RepresentablePresheaf Simplicial

universe u

section

variable (U : SSet.{u}) (n : ℕ)

/- The underlying representable-to-slice equivalence. -/
#check
  (RepresentablePresheaf.Elements.overEquivalence ⦋n⦌ :
    h[⦋n⦌].Elementsᵒᵖ ≌ Over ⦋n⦌)

/- Example 14.11.4 (1): the category `Δ/[n] → Δ`, viewed as fibred in sets over `Δ`, is
the category of elements of the representable presheaf at `⦋n⦌`. -/
@[stacks 0178 "Example 14.11.4 (1)"]
#check (RepresentablePresheaf.Elements.fiberedEquivalence ⦋n⦌ :
  FiberedCategoryOver.Sets.ofFunctor
      ((CategoryTheory.CategoryOfElements.π h[⦋n⦌]).leftOp) ≌
    FiberedCategoryOver.Sets.ofFunctor (Over.forget ⦋n⦌))

/- Since the standard simplex `Δ[n]` is the simplicial representable at `⦋n⦌`, the resulting
presheaf formula for maps into `U` is the canonical simplicial Yoneda equivalence. -/
@[stacks 0178 "Example 14.11.4 (2)"]
#check (SSet.yonedaEquiv : (Δ[n] ⟶ U) ≃ U _⦋n⦌)

end
