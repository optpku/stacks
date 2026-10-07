module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 08NL

# Trivial Kan fibrations

This file supplements the canonical morphism property `SSet.modelCategoryQuillen.I.rlp` with
its source-facing boundary-filling decomposition. More specialized criteria live in dedicated
leaf modules.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u

namespace SSet.modelCategoryQuillen

variable {X Y : SSet.{u}} (f : X ⟶ Y)

namespace I

namespace rlp

/-- Every morphism lifting against all simplex boundaries is a Kan fibration. -/
@[stacks 08NL "trivial Kan fibrations are Kan fibrations"]
theorem le_fibrations :
    I.rlp ≤ HomotopicalAlgebra.fibrations SSet.{u} := sorry

namespace boundary

/-- A morphism in `I.rlp` lifts against each individual simplex boundary inclusion. -/
@[stacks 08NL "boundary lifting for trivial Kan fibrations"]
theorem hasLiftingProperty (n : ℕ) (hf : I.rlp f) :
    HasLiftingProperty (∂Δ[n].ι) f := sorry

end boundary

namespace zero

/-- A morphism in `I.rlp` is surjective on vertices. -/
@[stacks 08NL "vertex surjectivity of trivial Kan fibrations"]
theorem surjective (hf : I.rlp f) :
    Function.Surjective (f.app (op ⦋0⦌)) := sorry

end zero

namespace boundary

/-- Vertex surjectivity together with all positive-dimensional boundary fillers implies membership
in `I.rlp`. -/
@[stacks 08NL "boundary-filling criterion for trivial Kan fibrations"]
theorem of_zero_surjective
    (h0 : Function.Surjective (f.app (op ⦋0⦌)))
    (hboundary : ∀ n : ℕ, HasLiftingProperty (∂Δ[n + 1].ι) f) :
    I.rlp f := sorry

/-- Membership in `I.rlp` is equivalent to vertex surjectivity and positive-dimensional boundary
fillers. -/
@[stacks 08NL "characterization of trivial Kan fibrations by boundary fillers"]
theorem iff_zero_surjective :
    I.rlp f ↔
      Function.Surjective (f.app (op ⦋0⦌)) ∧
        ∀ n : ℕ, HasLiftingProperty (∂Δ[n + 1].ι) f := sorry

end boundary

end rlp

end I

end SSet.modelCategoryQuillen
