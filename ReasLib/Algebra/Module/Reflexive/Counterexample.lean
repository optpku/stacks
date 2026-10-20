/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import ReasLib.Algebra.Module.Reflexive
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition

/-!
# A reflexive module over a ring which is not `(S₂)`

The explicit affine-algebra example separates reflexivity of a finite module from Serre's
condition on the base ring.  The algebra, ideal, multiplication maps, and linear equivalences
are concrete data; only their algebraic laws and bijectivity proofs are deferred.
-/

@[expose] public section

open MvPolynomial

universe u

namespace Module.ReflexiveCounterexample

noncomputable section

/-- The ambient polynomial ring `k[x, y]` in the reflexive counterexample. -/
@[stacks 0EBB "ambient polynomial ring of the reflexive counterexample"]
abbrev PolynomialRing (k : Type u) [CommSemiring k] := MvPolynomial (Fin 2) k

variable (k : Type u) [Field k]

/-- The variable `x` in the ambient polynomial ring. -/
@[stacks 0EBB "first variable of the reflexive counterexample"]
def x : PolynomialRing k := X (0 : Fin 2)

/-- The variable `y` in the ambient polynomial ring. -/
@[stacks 0EBB "second variable of the reflexive counterexample"]
def y : PolynomialRing k := X (1 : Fin 2)

/-- The subalgebra `R = k[y, x^2, xy, x^3]` of `k[x, y]`. -/
@[stacks 0EBB "Example 15.23.17 (1)"]
def ring : Subalgebra k (PolynomialRing k) :=
  Algebra.adjoin k ({y k, x k ^ 2, x k * y k, x k ^ 3} : Set (PolynomialRing k))

/-- The generator `y` belongs to `ring k`. -/
theorem y_mem_ring : y k ∈ ring k := sorry

/-- The generator `x^2` belongs to `ring k`. -/
theorem xSq_mem_ring : x k ^ 2 ∈ ring k := sorry

/-- The generator `xy` belongs to `ring k`. -/
theorem xy_mem_ring : x k * y k ∈ ring k := sorry

/-- The generator `x^3` belongs to `ring k`. -/
theorem xCube_mem_ring : x k ^ 3 ∈ ring k := sorry

/-- The generator `y`, regarded as an element of `ring k`. -/
@[stacks 0EBB "y generator of the counterexample ideal"]
def idealGeneratorY : ring k := ⟨y k, y_mem_ring k⟩

/-- The generator `x^2`, regarded as an element of `ring k`. -/
@[stacks 0EBB "x-squared generator of the counterexample ideal"]
def idealGeneratorXSq : ring k := ⟨x k ^ 2, xSq_mem_ring k⟩

/-- The generator `xy`, regarded as an element of `ring k`. -/
@[stacks 0EBB "xy generator of the counterexample ideal"]
def idealGeneratorXY : ring k := ⟨x k * y k, xy_mem_ring k⟩

/-- The generator `x^3`, regarded as an element of `ring k`. -/
@[stacks 0EBB "x-cubed generator of the counterexample ideal"]
def idealGeneratorXCube : ring k := ⟨x k ^ 3, xCube_mem_ring k⟩

/-- The four-element generating set for the origin ideal. -/
@[stacks 0EBB "generating set of the counterexample ideal"]
def idealGeneratorSet : Set (ring k) :=
  {idealGeneratorY k, idealGeneratorXSq k, idealGeneratorXY k, idealGeneratorXCube k}

/-- The ideal `𝔪 = (y, x^2, xy, x^3)` in `ring k`. -/
@[stacks 0EBB "Example 15.23.17 (2)"]
def ideal : Ideal (ring k) := Ideal.span (idealGeneratorSet k)

-- Local instance justification (defeq pin): use the subalgebra action defining the ambient
-- polynomial ring as a module over the counterexample subalgebra.
local instance : Module (ring k) (PolynomialRing k) := Subalgebra.moduleLeft (ring k)

-- Local instance justification (defeq pin): use the distinguished ideal's inherited subtype
-- action throughout both duals.
local instance : Module (ring k) (ideal k) := SMulMemClass.toModule (ideal k)

/-- The ambient polynomial ring as a bundled module over the counterexample subalgebra. -/
def ambientModule : ModuleCat (ring k) := ModuleCat.of (ring k) (PolynomialRing k)

/-- Multiplication by an element of `ideal k` sends every ambient polynomial back into `ring k`. -/
theorem ideal_mul_mem_ring (a : ideal k) (p : PolynomialRing k) :
    ((a : ring k) : PolynomialRing k) * p ∈ ring k := sorry

/-- Multiplication by an ideal element, packaged as an element of the subalgebra. -/
@[stacks 0EBB "multiplication into the counterexample subalgebra"]
def mulIntoRing (a : ideal k) (p : PolynomialRing k) : ring k :=
  ⟨((a : ring k) : PolynomialRing k) * p, ideal_mul_mem_ring k a p⟩

/-- `mulIntoRing` is additive in its ambient-polynomial argument. -/
theorem mulIntoRing_add_right (a : ideal k) (p q : PolynomialRing k) :
    mulIntoRing k a (p + q) = mulIntoRing k a p + mulIntoRing k a q := sorry

/-- `mulIntoRing` is linear in its ambient-polynomial argument. -/
theorem mulIntoRing_smul_right (a : ideal k) (r : ring k) (p : PolynomialRing k) :
    mulIntoRing k a (r • p) = r • mulIntoRing k a p := sorry

/-- `mulIntoRing` is additive in its ideal argument. -/
theorem mulIntoRing_add_left (a b : ideal k) (p : PolynomialRing k) :
    mulIntoRing k (a + b) p = mulIntoRing k a p + mulIntoRing k b p := sorry

/-- `mulIntoRing` is linear in its ideal argument. -/
theorem mulIntoRing_smul_left (r : ring k) (a : ideal k) (p : PolynomialRing k) :
    mulIntoRing k (r • a) p = r • mulIntoRing k a p := sorry

/-- Multiplication by one ideal element as an `ring k`-linear functional on `k[x, y]`. -/
@[stacks 0EBB "action of an ideal element on the ambient polynomial ring"]
def idealElementAction (a : ideal k) : Dual (ring k) (PolynomialRing k) where
  toFun := mulIntoRing k a
  map_add' := mulIntoRing_add_right k a
  map_smul' := mulIntoRing_smul_right k a

/-- `idealElementAction` preserves addition of ideal elements. -/
theorem idealElementAction_add (a b : ideal k) :
    idealElementAction k (a + b) = idealElementAction k a + idealElementAction k b := sorry

/-- `idealElementAction` preserves scalar multiplication of ideal elements. -/
theorem idealElementAction_smul (r : ring k) (a : ideal k) :
    idealElementAction k (r • a) = r • idealElementAction k a := sorry

/-- The multiplication map `𝔪 → Hom_R(k[x, y], R)`. -/
@[stacks 0EBB "map from the ideal to the ambient dual"]
def idealToAmbientDual : ideal k →ₗ[ring k] Dual (ring k) (PolynomialRing k) where
  toFun := idealElementAction k
  map_add' := idealElementAction_add k
  map_smul' := idealElementAction_smul k

/-- Evaluation at `1` of an ambient dual functional belongs to the origin ideal. -/
theorem ambientDual_evalOne_mem_ideal (φ : Dual (ring k) (PolynomialRing k)) :
    φ 1 ∈ ideal k := sorry

/-- Evaluation at `1`, with its proof of membership in the origin ideal. -/
@[stacks 0EBB "evaluation at one into the counterexample ideal"]
def ambientDualAtOne (φ : Dual (ring k) (PolynomialRing k)) : ideal k :=
  ⟨φ 1, ambientDual_evalOne_mem_ideal k φ⟩

/-- `ambientDualAtOne` preserves addition. -/
theorem ambientDualAtOne_add (φ ψ : Dual (ring k) (PolynomialRing k)) :
    ambientDualAtOne k (φ + ψ) = ambientDualAtOne k φ + ambientDualAtOne k ψ := sorry

/-- `ambientDualAtOne` preserves scalar multiplication. -/
theorem ambientDualAtOne_smul (r : ring k) (φ : Dual (ring k) (PolynomialRing k)) :
    ambientDualAtOne k (r • φ) = r • ambientDualAtOne k φ := sorry

/-- Evaluation at `1` as the linear map `Hom_R(k[x, y], R) → 𝔪`. -/
@[stacks 0EBB "ambient-dual evaluation map to the ideal"]
def ambientDualToIdeal : Dual (ring k) (PolynomialRing k) →ₗ[ring k] ideal k where
  toFun := ambientDualAtOne k
  map_add' := ambientDualAtOne_add k
  map_smul' := ambientDualAtOne_smul k

/-- Evaluation at `1` is bijective, with inverse given by multiplication. -/
theorem ambientDualToIdeal_bijective : Function.Bijective (ambientDualToIdeal k) := sorry

/-- Evaluation at `1` followed by multiplication is the identity on the origin ideal. -/
theorem ambientDualToIdeal_comp_idealToAmbientDual :
    (ambientDualToIdeal k).comp (idealToAmbientDual k) = LinearMap.id := sorry

/-- Multiplication followed by evaluation at `1` is the identity on the ambient dual. -/
theorem idealToAmbientDual_comp_ambientDualToIdeal :
    (idealToAmbientDual k).comp (ambientDualToIdeal k) = LinearMap.id := sorry

/-- The linear identification `Hom_R(k[x, y], R) ≃ 𝔪`. -/
@[stacks 0EBB "Example 15.23.17 (3)"]
noncomputable def ambientDualEquivIdeal :
    Dual (ring k) (PolynomialRing k) ≃ₗ[ring k] ideal k :=
  LinearEquiv.ofLinear (ambientDualToIdeal k) (idealToAmbientDual k)
    (ambientDualToIdeal_comp_idealToAmbientDual k)
    (idealToAmbientDual_comp_ambientDualToIdeal k)

/-- The equivalence `ambientDualEquivIdeal k` sends a functional to its value at `1`. -/
@[simp]
theorem ambientDualEquivIdeal_apply (φ : Dual (ring k) (PolynomialRing k)) :
    ambientDualEquivIdeal k φ = ambientDualAtOne k φ := sorry

/-- The inverse of `ambientDualEquivIdeal k` is multiplication by an ideal element. -/
@[simp]
theorem ambientDualEquivIdeal_symm_apply (a : ideal k) :
    (ambientDualEquivIdeal k).symm a = idealElementAction k a := sorry

/-- Evaluation at `1` uniquely determines `ambientDualEquivIdeal k`. -/
theorem ambientDualEquivIdeal_unique
    (e : Dual (ring k) (PolynomialRing k) ≃ₗ[ring k] ideal k)
    (h : e.toLinearMap = ambientDualToIdeal k) : e = ambientDualEquivIdeal k := sorry

/-- Multiplication by an ambient polynomial as a functional on the origin ideal. -/
@[stacks 0EBB "action of an ambient polynomial on the ideal"]
def ambientElementAction (p : PolynomialRing k) : Dual (ring k) (ideal k) where
  toFun := fun a ↦ mulIntoRing k a p
  map_add' := fun a b ↦ mulIntoRing_add_left k a b p
  map_smul' := fun r a ↦ mulIntoRing_smul_left k r a p

/-- `ambientElementAction` preserves addition of ambient polynomials. -/
theorem ambientElementAction_add (p q : PolynomialRing k) :
    ambientElementAction k (p + q) = ambientElementAction k p + ambientElementAction k q := sorry

/-- `ambientElementAction` preserves scalar multiplication of ambient polynomials. -/
theorem ambientElementAction_smul (r : ring k) (p : PolynomialRing k) :
    ambientElementAction k (r • p) = r • ambientElementAction k p := sorry

/-- The multiplication map `k[x, y] → Hom_R(𝔪, R)`. -/
@[stacks 0EBB "map from ambient polynomials to the ideal dual"]
def ambientToIdealDual : PolynomialRing k →ₗ[ring k] Dual (ring k) (ideal k) where
  toFun := ambientElementAction k
  map_add' := ambientElementAction_add k
  map_smul' := ambientElementAction_smul k

/-- Multiplication identifies `k[x, y]` bijectively with `Hom_R(𝔪, R)`. -/
theorem ambientToIdealDual_bijective : Function.Bijective (ambientToIdealDual k) := sorry

/-- The linear identification `Hom_R(𝔪, R) ≃ k[x, y]`, parametrized by
an explicit bijectivity proof for the multiplication map. -/
@[stacks 0EBB "Example 15.23.17 (4)"]
noncomputable def idealDualEquivAmbientOf
    (hbij : Function.Bijective (ambientToIdealDual k)) :
    Dual (ring k) (ideal k) ≃ₗ[ring k] PolynomialRing k :=
  (LinearEquiv.ofBijective (ambientToIdealDual k) hbij).symm

/-- The inverse of `idealDualEquivAmbientOf k hbij` is multiplication by an ambient polynomial. -/
@[simp]
theorem idealDualEquivAmbientOf_symm_apply
    (hbij : Function.Bijective (ambientToIdealDual k)) (p : PolynomialRing k) :
    (idealDualEquivAmbientOf k hbij).symm p = ambientElementAction k p := sorry

/-- The multiplication map `ambientToIdealDual k` uniquely determines
`idealDualEquivAmbientOf k hbij`. -/
theorem idealDualEquivAmbientOf_unique
    (hbij : Function.Bijective (ambientToIdealDual k))
    (e : Dual (ring k) (ideal k) ≃ₗ[ring k] PolynomialRing k)
    (h : e.symm.toLinearMap = ambientToIdealDual k) : e = idealDualEquivAmbientOf k hbij := sorry

/-- The equivalence `idealDualEquivAmbientOf k hbij` is independent of the chosen proof that
`ambientToIdealDual k` is bijective. -/
theorem idealDualEquivAmbientOf_congr
    (hbij hbij' : Function.Bijective (ambientToIdealDual k)) :
    idealDualEquivAmbientOf k hbij = idealDualEquivAmbientOf k hbij' := sorry

/-- The counterexample ring is Noetherian. -/
@[stacks 0EBB "Example 15.23.17 (5)"]
instance ringIsNoetherian : IsNoetherianRing (ring k) := sorry

/-- The ambient polynomial ring is finite as a module over `ring k`. -/
@[stacks 0EBB "Example 15.23.17 (6)"]
instance ambientModuleFinite : Module.Finite (ring k) (PolynomialRing k) := sorry

/-- The ambient polynomial ring is reflexive as an `ring k`-module. -/
@[stacks 0EBB "Example 15.23.17 (7)"]
theorem ambient_isReflexive : Module.IsReflexive (ring k) (PolynomialRing k) := sorry

/-- The ambient polynomial ring satisfies module `(S₂)`. -/
@[stacks 0EBB "Example 15.23.17 (8)"]
theorem ambient_serreConditionSTwo : Module.SerreConditionS (ring k) (PolynomialRing k) 2 := sorry

/-- The counterexample ring itself does not satisfy `(S₂)`. -/
@[stacks 0EBB "Example 15.23.17 (9)"]
theorem ring_not_serreConditionSTwo : ¬ ((ring k) ⊧ (S₂)) := sorry

end

end Module.ReflexiveCounterexample
