/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Effective
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Principal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ClosedPoint

/-!
# Classical Riemann–Roch spaces of Weil divisors

The spaces `L(D)` and dimensions `l(D)` of rational functions with `(f) + D`
effective, assuming DVR stalks at prime divisors. On a general singular curve,
the length-order constraint only defines `riemannRochOrderSet`: it need not be
closed under addition. No span is used to enlarge this set.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The raw length-order constraint, including zero. On a nonnormal curve this
set need not be closed under addition; no vector space structure is asserted. -/
def riemannRochOrderSet {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
    [IsLocallyNoetherian X.left] (D : Div(X.left)) :
    Set X.left.functionField :=
  {f | f = 0 ∨ ∃ hf : f ≠ 0,
    WeilDivisor.IsEffective (principalWeilDivisor X.left (Units.mk0 f hf) + D)}

/-- The underlying set of the classical Riemann–Roch space `L(D)`. The DVR
hypothesis makes the orders valuations; `riemannRochSubmodule` packages exactly
this set as a vector space with the structural `k`-action. -/
def riemannRochSpace {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
    [IsLocallyNoetherian X.left] [PrimeDivisorDiscreteValuationRings X.left]
    (D : Div(X.left)) : Set X.left.functionField :=
  riemannRochOrderSet X D

/-- Membership in `L(D)` is vanishing or effectivity of `(f) + D`. -/
theorem mem_riemannRochSpace {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
    [IsLocallyNoetherian X.left] [PrimeDivisorDiscreteValuationRings X.left]
    (D : Div(X.left))
    (f : X.left.functionField) :
    f ∈ riemannRochSpace X D ↔
      f = 0 ∨ ∃ hf : f ≠ 0,
        WeilDivisor.IsEffective (principalWeilDivisor X.left (Units.mk0 f hf) + D) := Iff.rfl

/-- The zero function lies in every Riemann–Roch space. -/
theorem zero_mem_riemannRochSpace {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
    [IsLocallyNoetherian X.left] [PrimeDivisorDiscreteValuationRings X.left]
    (D : Div(X.left)) :
    0 ∈ riemannRochSpace X D := by
  exact Or.inl rfl

/-- Addition preserves the divisor bound when the prime-divisor stalks are DVRs. -/
theorem add_mem_riemannRochSpace {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
    [IsLocallyNoetherian X.left] [PrimeDivisorDiscreteValuationRings X.left]
    (D : Div(X.left)) {f g : X.left.functionField}
    (hf : f ∈ riemannRochSpace X D) (hg : g ∈ riemannRochSpace X D) :
    f + g ∈ riemannRochSpace X D := by
  rcases hf with rfl | ⟨hf, hD⟩
  · simpa using hg
  rcases hg with rfl | ⟨hg, hE⟩
  · rw [add_zero]
    exact Or.inr ⟨hf, hD⟩
  by_cases hfg : f + g = 0
  · exact Or.inl hfg
  refine Or.inr ⟨hfg, fun Z ↦ ?_⟩
  letI := primeDivisorDiscreteValuationRing X.left Z
  have hadd := X.left.ord_add (x := Z.genericPoint) hfg
  have hmin : -D.coeff Z ≤ min (X.left.ord f Z.genericPoint)
      (X.left.ord g Z.genericPoint) := by
    apply le_min
    · have h := hD Z
      change 0 ≤ X.left.ord f Z.genericPoint + D.coeff Z at h
      omega
    · have h := hE Z
      change 0 ≤ X.left.ord g Z.genericPoint + D.coeff Z at h
      omega
  change 0 ≤ X.left.ord (f + g) Z.genericPoint + D.coeff Z
  have := hmin.trans hadd
  omega

set_option backward.isDefEq.respectTransparency false in
private theorem functionFieldAlgebraMap_eq_stalk {k : Type u} [Field k]
    (X : SchemeOverField k) [Variety X] (x : X.left) (a : k) :
    SchemeOverField.functionFieldAlgebraMap X a =
      algebraMap (X.left.presheaf.stalk x) X.left.functionField
        (X.hom.stalkMap x (StructureSheaf.toStalk k (X.hom x) a)) := by
  let h := (genericPoint_spec X.left).specializes (Set.mem_univ x)
  have he := LocallyRingedSpace.stalkSpecializes_stalkMap
    X.hom.toLRSHom (genericPoint X.left) x h
  have he' := congrArg
    (fun q ↦ StructureSheaf.toStalk k (X.hom x) ≫ q) he
  rw [← CategoryTheory.Category.assoc] at he'
  erw [StructureSheaf.toStalk_stalkSpecializes] at he'
  exact (CategoryTheory.ConcreteCategory.congr_hom he' a)

private theorem ord_functionFieldAlgebraMap {k : Type u} [Field k]
    (X : SchemeOverField k) [Variety X] [IsLocallyNoetherian X.left]
    (x : X.left) {a : k} (ha : a ≠ 0) :
    X.left.ord (SchemeOverField.functionFieldAlgebraMap X a) x = 0 := by
  rw [functionFieldAlgebraMap_eq_stalk X x a]
  have hu : IsUnit (X.hom.stalkMap x (StructureSheaf.toStalk k (X.hom x) a)) :=
    ((isUnit_iff_ne_zero.mpr ha).map (StructureSheaf.toStalk k (X.hom x)).hom).map
      (X.hom.stalkMap x).hom
  by_cases hx : Order.coheight x = 1
  · letI : Ring.KrullDimLE 1 (X.left.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    rw [ord_eq_ordHom_of_coheight_eq_one hx]
    change Multiplicative.toAdd ((Ring.ordFrac (X.left.presheaf.stalk x)
      (algebraMap (X.left.presheaf.stalk x) X.left.functionField _)).unzeroD 1) = 0
    simp [Ring.ordFrac_of_isUnit hu]
  · exact X.left.ord_eq_zero_of_coheight_neq_one hx _

/-- The structural `k`-action preserves the divisor bound. -/
theorem smul_mem_riemannRochSpace {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
    [IsLocallyNoetherian X.left] [PrimeDivisorDiscreteValuationRings X.left]
    (D : Div(X.left)) (a : k) {f : SchemeOverField.functionFieldCommAlg X}
    (hf : f ∈ riemannRochSpace X D) : a • f ∈ riemannRochSpace X D := by
  rcases hf with rfl | ⟨hf, hD⟩
  · exact Or.inl (smul_zero a : a • (0 : SchemeOverField.functionFieldCommAlg X) = 0)
  by_cases ha : a = 0
  · subst a
    exact Or.inl (zero_smul k f)
  have ha' : SchemeOverField.functionFieldAlgebraMap X a ≠ 0 :=
    (map_ne_zero (SchemeOverField.functionFieldAlgebraMap X)).mpr ha
  have haf : a • f ≠ 0 := smul_ne_zero ha hf
  refine Or.inr ⟨haf, fun Z ↦ ?_⟩
  let f' : X.left.functionField := f
  change 0 ≤ X.left.ord (SchemeOverField.functionFieldAlgebraMap X a *
    f')
    Z.genericPoint + D.coeff Z
  rw [X.left.ord_mul ha' hf, ord_functionFieldAlgebraMap X Z.genericPoint ha, zero_add]
  exact hD Z

/-- The classical `k`-submodule `L(D)`, with exactly the order-constraint carrier.
The scalar structure is the one induced by `X ⟶ Spec k`. -/
def riemannRochSubmodule {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
    [IsLocallyNoetherian X.left] [PrimeDivisorDiscreteValuationRings X.left]
    (D : Div(X.left)) : Submodule k (SchemeOverField.functionFieldCommAlg X) where
  carrier := riemannRochSpace X D
  zero_mem' := zero_mem_riemannRochSpace X D
  add_mem' := add_mem_riemannRochSpace X D
  smul_mem' := smul_mem_riemannRochSpace X D

/-- The submodule carrier is exactly the raw order set, without taking a span. -/
theorem coe_riemannRochSubmodule {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
    [IsLocallyNoetherian X.left] [PrimeDivisorDiscreteValuationRings X.left]
    (D : Div(X.left)) :
    (riemannRochSubmodule X D : Set (SchemeOverField.functionFieldCommAlg X)) =
      riemannRochOrderSet X D := rfl

/-- Membership in the classical submodule is exactly the original divisor bound. -/
theorem mem_riemannRochSubmodule {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
    [IsLocallyNoetherian X.left] [PrimeDivisorDiscreteValuationRings X.left]
    (D : Div(X.left)) (f : SchemeOverField.functionFieldCommAlg X) :
    f ∈ riemannRochSubmodule X D ↔
      f = 0 ∨ ∃ hf : f ≠ 0,
        WeilDivisor.IsEffective (principalWeilDivisor X.left (Units.mk0 f hf) + D) := Iff.rfl

/-- The dimension `l(D)` of the Riemann–Roch space as a `k`-vector space. -/
def riemannRochDim {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
    [IsLocallyNoetherian X.left] [PrimeDivisorDiscreteValuationRings X.left]
    (D : Div(X.left)) : ℕ :=
  Module.finrank k (riemannRochSubmodule X D)

/-- `l(D)` is the `k`-dimension of `L(D)` itself. -/
theorem riemannRochDim_eq_finrank {k : Type u} [Field k] (X : SchemeOverField k)
    [Variety X] [IsLocallyNoetherian X.left] [PrimeDivisorDiscreteValuationRings X.left]
    (D : Div(X.left)) :
    riemannRochDim X D = Module.finrank k (riemannRochSubmodule X D) := rfl

end AlgebraicGeometry.Scheme
