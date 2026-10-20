/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Endpoints of the simplicial interval

This module owns the constant endpoint endomorphisms and endpoint simplices of `Δ[1]`. It also
assembles the two endpoint maps into the canonical monomorphism `X ⨿ X ⟶ X ⊗ Δ[1]`, avoiding
repeated reconstruction of the coproduct presentation in homotopy lifting arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open SSet (ι₀ ι₁)
open scoped MonoidalCategory Simplicial

universe u

namespace SSet

namespace deltaOne

/-- The constant endomorphism of `Δ[1]` with value the vertex `i`. -/
@[stacks 019O "constant endomorphism of the simplicial interval"]
noncomputable def const (i : Fin 2) :
    (Δ[1] : SSet.{u}) ⟶ Δ[1] :=
  SSet.const (stdSimplex.obj₀Equiv.symm i)

/-- The canonical `i`-endpoint simplex in each degree of the simplicial interval. -/
@[stacks 019O "endpoint simplex of the simplicial interval"]
noncomputable def endpoint (i : Fin 2) (m : SimplexCategoryᵒᵖ) :
    (Δ[1] : SSet.{u}).obj m :=
  stdSimplex.const 1 i m

/-- The endpoint owner is the degreewise constant simplex used by `deltaOne.const`. -/
@[simp, stacks 019O "endpoint simplex formula"]
theorem endpoint_apply (i : Fin 2) (m : SimplexCategoryᵒᵖ) :
    endpoint i m = stdSimplex.const 1 i m := sorry

namespace const

/-- Degreewise, `deltaOne.const i` is the constant simplex at `i`. -/
@[simp, stacks 019O "constant interval endpoint formula"]
theorem app_apply (i : Fin 2) (m : SimplexCategoryᵒᵖ)
    (x : (Δ[1] : SSet.{u}).obj m) :
    (SSet.deltaOne.const i).app m x = stdSimplex.const 1 i m := sorry

end const

end deltaOne

/-- The union of the two endpoint subcomplexes inside the simplicial cylinder `X ⊗ Δ[1]`.
This is the subcomplex presentation of `X ⊗ ∂Δ[1]`. -/
@[stacks 08NS "simplicial-cylinder endpoint subcomplex"]
def endpointSubcomplex (X : SSet.{u}) : (X ⊗ Δ[1]).Subcomplex :=
  (⊥ : X.Subcomplex).unionProd ∂Δ[1]

/-- The inclusion of the two endpoints into the simplicial cylinder `X ⊗ Δ[1]`. -/
@[stacks 08NS "simplicial-cylinder endpoint inclusion"]
noncomputable def endpointInclusion (X : SSet.{u}) : X ⨿ X ⟶ X ⊗ Δ[1] :=
  coprod.desc (ι₀ : X ⟶ X ⊗ Δ[1]) ι₁

/-- The endpoint inclusion restricts to the zero endpoint on the left summand. -/
@[simp, reassoc, stacks 08NS "left summand of the simplicial-cylinder endpoint inclusion"]
theorem inl_endpointInclusion (X : SSet.{u}) :
    (coprod.inl : X ⟶ X ⨿ X) ≫ endpointInclusion X = ι₀ := sorry

/-- The endpoint inclusion restricts to the one endpoint on the right summand. -/
@[simp, reassoc, stacks 08NS "right summand of the simplicial-cylinder endpoint inclusion"]
theorem inr_endpointInclusion (X : SSet.{u}) :
    (coprod.inr : X ⟶ X ⨿ X) ≫ endpointInclusion X = ι₁ := sorry

/-- The inclusion of the two endpoints of a simplicial cylinder is a monomorphism. -/
@[stacks 08NS "endpoint inclusion is mono"]
instance endpointInclusion_mono (X : SSet.{u}) : Mono (endpointInclusion X) := sorry

namespace endpointInclusion

/-- The range of the coproduct presentation of the endpoint inclusion is the canonical endpoint
subcomplex of the simplicial cylinder. -/
@[stacks 08NS "range of the simplicial-cylinder endpoint inclusion"]
theorem range (X : SSet.{u}) :
    Subcomplex.range (endpointInclusion X) = endpointSubcomplex X := sorry

/-- Equation 25.9.1.2 (Tag 01GR), in functorial form: a map of simplicial sets carries the
two cylinder endpoints to the corresponding endpoints of the target cylinder. -/
@[stacks 01GR "naturality of the simplicial-cylinder endpoint inclusion"]
theorem naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    CommSq (coprod.map f f) (endpointInclusion X) (endpointInclusion Y)
      (f ▷ (Δ[1] : SSet.{u})) := sorry

end endpointInclusion

end SSet
