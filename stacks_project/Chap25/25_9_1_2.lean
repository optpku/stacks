/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.DeltaOne.Endpoint
import StacksCheckRecall

/-! # Naturality of the simplicial-cylinder endpoints -/

open CategoryTheory
open scoped Simplicial

universe u

variable (n : ℕ)

/- Equation 25.9.1.2 (01GR) is endpoint-inclusion naturality specialized to the boundary
inclusion `∂Δ[n + 1] ⟶ Δ[n + 1]`. -/
@[stacks 01GR] #check
  SSet.endpointInclusion.naturality
    ((∂Δ[n + 1]).ι : (∂Δ[n + 1] : SSet.{u}) ⟶ Δ[n + 1])

/- The pushout used to form the union of the boundary cylinder and the two endpoint copies is
the canonical `Subcomplex.unionProd` pushout. -/
#check SSet.Subcomplex.unionProd.isPushout
  (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex)
  (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex)
