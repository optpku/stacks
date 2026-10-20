module

public import ReasLib.AlgebraicTopology.SimplicialSet.DeltaOne.Order
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# Canonical homotopies of the simplicial interval

Pointwise maximum contracts `Δ[1]` toward its final vertex, while pointwise minimum expands it
from its initial vertex. The underlying maps are owned by the order-theoretic leaf; this module
packages their endpoint laws as reusable `SSet.Homotopy` data.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

noncomputable section

universe u

namespace SSet.deltaOne

namespace max.map

/-- The maximum map satisfies the vacuous relative condition on the bottom subcomplex. -/
theorem rel :
    (⊥ : (Δ[1] : SSet.{u}).Subcomplex).ι ▷ (Δ[1] : SSet.{u}) ≫
        SSet.deltaOne.max.map =
      fst _ _ ≫
        Subcomplex.isInitialBot.to ((⊥ : (Δ[1] : SSet.{u}).Subcomplex).toSSet) ≫
          (⊥ : (Δ[1] : SSet.{u}).Subcomplex).ι := sorry

end max.map

namespace max

/-- Lemma 14.26.8: pointwise maximum is a directed homotopy from the identity of `Δ[1]`
to the constant-one endomorphism. -/
@[stacks 019O "maximum homotopy of the simplicial interval"]
noncomputable def homotopy :
    Homotopy (𝟙 (Δ[1] : SSet.{u})) (SSet.deltaOne.const (1 : Fin 2)) where
  h := SSet.deltaOne.max.map
  h₀ := SSet.deltaOne.max.map.ι₀_comp
  h₁ := SSet.deltaOne.max.map.ι₁_comp
  rel := SSet.deltaOne.max.map.rel

end max

namespace min.map

/-- The minimum map satisfies the vacuous relative condition on the bottom subcomplex. -/
theorem rel :
    (⊥ : (Δ[1] : SSet.{u}).Subcomplex).ι ▷ (Δ[1] : SSet.{u}) ≫
        SSet.deltaOne.min.map =
      fst _ _ ≫
        Subcomplex.isInitialBot.to ((⊥ : (Δ[1] : SSet.{u}).Subcomplex).toSSet) ≫
          (⊥ : (Δ[1] : SSet.{u}).Subcomplex).ι := sorry

end min.map

namespace min

/-- Lemma 14.26.8: pointwise minimum is a directed homotopy from the constant-zero
endomorphism of `Δ[1]` to its identity. -/
@[stacks 019O "minimum homotopy of the simplicial interval"]
noncomputable def homotopy :
    Homotopy (SSet.deltaOne.const (0 : Fin 2)) (𝟙 (Δ[1] : SSet.{u})) where
  h := SSet.deltaOne.min.map
  h₀ := SSet.deltaOne.min.map.ι₀_comp
  h₁ := SSet.deltaOne.min.map.ι₁_comp
  rel := SSet.deltaOne.min.map.rel

end min

end SSet.deltaOne
