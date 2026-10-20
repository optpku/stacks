/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Finiteness
import StacksCheckRecall

@[expose] public section

/-!
@stack 017C

# Definition 14.13.1

The simplicial copower and its computation rules are owned by
`ReasLib.AlgebraicTopology.SimplicialObject.Copower`. This file records the source assumptions
under which binary coproducts suffice.
-/

open CategoryTheory
open CategoryTheory.Limits
open scoped Simplicial

noncomputable section

namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
variable (U : SSet.{w}) [U.ObjFinite] [U.Nonempty]
variable (V : SimplicialObject C)
variable (Δ : SimplexCategoryᵒᵖ)

/- Definition 14.13.1: the product of a degreewise finite nonempty simplicial set `U` and a
simplicial object `V` is the degreewise copower `SimplicialObject.copower U V`. -/
@[stacks 017C]
#check (SimplicialObject.copower U V : SimplicialObject C)

/- The source finiteness assumptions feed the reusable copower instance directly. -/
#check (SimplicialObject.HasCopowers.ofFiniteNonempty U :
  SimplicialObject.HasCopowers U C)

/- Its object in degree `Δ` is the coproduct of the `U.obj Δ`-indexed family constant at
`V.obj Δ`. -/
#check (SimplicialObject.copower.obj U V Δ :
  (SimplicialObject.copower U V).obj Δ = ∐ (fun _ : U.obj Δ ↦ V.obj Δ))

/- Its structure maps reindex summands through `U` and apply the structure maps of `V`. -/
variable {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ')

#check (SimplicialObject.copower.map U V f :
  (SimplicialObject.copower U V).map f =
    Sigma.map' (U.map f) (fun _ ↦ V.map f))

end CategoryTheory
