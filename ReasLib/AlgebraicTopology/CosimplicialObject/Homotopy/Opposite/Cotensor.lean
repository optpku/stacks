module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Opposite
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.DeltaOne.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 019X

# Cotensor comparison across opposite cosimplicial objects

The opposite presentation is defined for arbitrary coefficient categories using the componentwise
`Δ[1]` relation. This leaf adds the source-facing cotensor formulation when the single displayed
cotensor exists, without forcing finite products on the general opposite bridge.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {U V : CosimplicialObject C} {a b : U ⟶ V}

section

variable [HasCotensor (Δ[1] : SSet.{0}) V]

/-- The cotensor-valued cosimplicial homotopy relation agrees with the opposite simplicial
homotopy relation through the product-free comparison. -/
@[stacks 019X "cotensor and opposite simplicial homotopy relation"]
theorem Homotopic.iff_op (a b : U ⟶ V) :
    Homotopic a b ↔
      SimplicialObject.Homotopic (NatTrans.op a) (NatTrans.op b) := sorry

end

end CategoryTheory.CosimplicialObject

end
