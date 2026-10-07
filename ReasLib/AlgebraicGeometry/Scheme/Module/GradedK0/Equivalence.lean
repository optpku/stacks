module

public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedK0

/-!
# Cycles as a dimension-graded Grothendieck group

This file identifies cycles of a fixed relative dimension with the Grothendieck group of the
corresponding quotient of coherent sheaves by lower-dimensional coherent sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.GradedK0

variable {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ)

/-- Taking the associated degree-`k` cycle after forming the positive-minus-negative
point-closure class is the identity. -/
theorem toCycle_toK0
    (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    toCycle f δ k (toK0 f δ k α) = α := sorry

/-- The positive-minus-negative point-closure class of the associated cycle of a coherent
object agrees with its class in the graded Grothendieck group. -/
theorem toK0_objectCycle
    (F : RingedSpace.CohLE X.toRingedSpace (f.relativeDimensionFunction δ) k) :
    toK0 f δ k (objectCycle f δ k F) = of f δ k F := sorry

/-- Forming the positive-minus-negative point-closure class after taking the associated
degree-`k` cycle is the identity on the graded Grothendieck group. -/
theorem toK0_toCycle (x : GradedK0 f δ k) :
    toK0 f δ k (toCycle f δ k x) = x := sorry

/-- The additive equivalence between degree-`k` cycles and the Grothendieck group of
`Coh≤k(X) / Coh≤k-1(X)`. -/
noncomputable def equiv :
    CycleGroup X (f.relativeDimensionFunction δ) k ≃+
      GradedK0 f δ k where
  toFun := toK0 f δ k
  invFun := toCycle f δ k
  left_inv := toCycle_toK0 f δ k
  right_inv := toK0_toCycle f δ k
  map_add' := (toK0 f δ k).map_add

/-- The forward function of `equiv` is `toK0`. -/
theorem equiv_apply (α : CycleGroup X (f.relativeDimensionFunction δ) k) :
    equiv f δ k α = toK0 f δ k α := sorry

/-- The inverse function of `equiv` is `toCycle`. -/
theorem equiv_symm_apply (x : GradedK0 f δ k) :
    (equiv f δ k).symm x = toCycle f δ k x := sorry

end AlgebraicGeometry.Scheme.Modules.GradedK0
