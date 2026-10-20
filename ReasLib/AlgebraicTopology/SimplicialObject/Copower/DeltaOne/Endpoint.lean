/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Finiteness
public import ReasLib.AlgebraicTopology.SimplicialSet.StdSimplexOne
public import ReasLib.AlgebraicTopology.SimplicialSet.DeltaOne.Endpoint
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Endpoints of the simplicial-interval copower

This module owns the two canonical endpoint maps into the simplicial cylinder and their
degreewise formulas.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject.copower.deltaOne

variable {C : Type u} [Category.{v} C]
variable (X : SimplicialObject C)
variable [HasCopower (Δ[1] : SSet.{w}) X]

/-- The degreewise coproduct injection selecting the constant simplex at the vertex `i`. -/
@[stacks 019O "simplicial cylinder endpoint component"]
def endpointApp (i : Fin 2) (m : SimplexCategoryᵒᵖ) :
    X.obj m ⟶ (SimplicialObject.copower (Δ[1] : SSet.{w}) X).obj m :=
  Sigma.ι (fun _ : (Δ[1] : SSet.{w}).obj m ↦ X.obj m)
    (SSet.deltaOne.endpoint i m)

/-- The degreewise endpoint injections commute with simplicial reindexing. -/
@[stacks 019O "simplicial cylinder endpoint component naturality"]
theorem endpointApp.naturality (i : Fin 2) {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) :
    X.map f ≫ endpointApp X i n =
      endpointApp X i m ≫ (SimplicialObject.copower (Δ[1] : SSet.{w}) X).map f := sorry

/-- Reindexing the simplicial copower by the constant endpoint endomorphism fixes the selected
endpoint summand. -/
@[reassoc (attr := simp), stacks 019O "endpoint summand under the canonical constant map"]
theorem endpointApp.indexHom (i : Fin 2) (m : SimplexCategoryᵒᵖ) :
    endpointApp X i m ≫
        (copower.indexHom X (SSet.deltaOne.const i)).app m =
      endpointApp X i m := sorry

/-- The endpoint map of the simplicial cylinder corresponding to the vertex `i : Fin 2`. -/
@[stacks 019O "endpoint of the simplicial copower cylinder"]
def endpoint (i : Fin 2) :
  X ⟶ SimplicialObject.copower (Δ[1] : SSet.{w}) X where
  app := endpointApp X i
  naturality := fun {_ _} f ↦ endpointApp.naturality X i f

/-- Degreewise formula for the endpoint map of the simplicial cylinder. -/
@[simp, stacks 019O "simplicial cylinder endpoint formula"]
theorem endpoint.app (i : Fin 2) (m : SimplexCategoryᵒᵖ) :
    (endpoint X i).app m = endpointApp X i m := sorry

/-- The zero-endpoint inclusion into the simplicial cylinder. -/
@[stacks 019O "zero endpoint of the simplicial copower cylinder"]
def endpointZero : X ⟶ SimplicialObject.copower (Δ[1] : SSet.{w}) X :=
  endpoint X (0 : Fin 2)

/-- The one-endpoint inclusion into the simplicial cylinder. -/
@[stacks 019O "one endpoint of the simplicial copower cylinder"]
def endpointOne : X ⟶ SimplicialObject.copower (Δ[1] : SSet.{w}) X :=
  endpoint X (1 : Fin 2)

section ObjectVariable

variable {X Y : SimplicialObject C}

/-- The endpoint inclusions are natural in the simplicial-object variable. -/
@[stacks 019O "simplicial cylinder endpoint naturality in the object variable"]
theorem endpoint.object.naturality
    [HasCopower (Δ[1] : SSet.{w}) X]
    [HasCopower (Δ[1] : SSet.{w}) Y]
    (i : Fin 2) (f : X ⟶ Y) :
    CommSq f (endpoint X i) (endpoint Y i)
      (copower.hom (Δ[1] : SSet.{w}) f) := sorry

variable [HasCopowers (Δ[1] : SSet.{w}) C]

/-- The endpoint inclusions assemble into a natural transformation from the identity to the
simplicial-cylinder functor. -/
@[stacks 019O "simplicial cylinder endpoint natural transformation"]
def endpoint.natTrans (i : Fin 2) :
    𝟭 (SimplicialObject C) ⟶ copower.functor (C := C) (Δ[1] : SSet.{w}) where
  app Y := endpoint Y i
  naturality := fun {_ _} f ↦ (endpoint.object.naturality i f).w

/-- The component of the endpoint natural transformation is the corresponding endpoint
inclusion. -/
@[simp, stacks 019O "simplicial cylinder endpoint natural-transformation component"]
theorem endpoint.natTrans.app (i : Fin 2) (Y : SimplicialObject C) :
    (endpoint.natTrans (C := C) i).app Y = endpoint Y i := sorry

end ObjectVariable

end CategoryTheory.SimplicialObject.copower.deltaOne
