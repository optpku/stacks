/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.Skeleton
import StacksCheckRecall

@[expose] public section

/-!
@stack 0191

# Source-facing bridge for Definition 14.22.3

The concentrated truncated object is owned by `Truncated.Single.Object`; its canonical Dold-Kan
skeleton model is imported directly from the mathematical `Skeleton` leaf.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (X : A) (k : ℕ)

/- Definition 14.22.3: `K(X, k)` is the left Kan extension of the truncated simplicial object
concentrated in degree `k`. -/
@[stacks 0191]
#check (SimplicialObject.eilenbergMacLane X k : SimplicialObject A)

/- The canonical skeleton comparison is a reusable companion to the source-facing object owner. -/
@[stacks 0191 "canonical skeleton comparison"]
#check (SimplicialObject.eilenbergMacLane.skeleton.iso (A := A) k :
  SimplicialObject.Truncated.concentrated.functor (A := A) k ⋙
      SimplicialObject.Truncated.sk k ≅
    SimplicialObject.eilenbergMacLane.functor k)
#check (SimplicialObject.Truncated.concentrated X k : SimplicialObject.Truncated A k)
#check (SimplicialObject.Truncated.concentrated.functor (A := A) k)
#check SimplicialObject.Truncated.concentrated.map
#check SimplicialObject.Truncated.concentrated.obj_top
#check SimplicialObject.Truncated.concentrated.map_eq
#check (SimplicialObject.eilenbergMacLane.functor (A := A) k)
#check (SimplicialObject.eilenbergMacLane.truncation.iso (A := A) k)
#check (SimplicialObject.eilenbergMacLane.truncation.objIso X k)
#check (SimplicialObject.eilenbergMacLane.truncation.iso_app (A := A) k X)
#check SimplicialObject.eilenbergMacLane.truncation.objIso.hom_naturality
#check SimplicialObject.eilenbergMacLane.truncation.objIso.inv_naturality
#check (SimplicialObject.eilenbergMacLane.skeleton.objIso (A := A) k X)
#check (SimplicialObject.eilenbergMacLane.skeleton.unit_hom (A := A) k X)
#check (SimplicialObject.eilenbergMacLane.skeleton.inv_unit (A := A) k X)
#check (SimplicialObject.eilenbergMacLane.skeleton.iso_app (A := A) k X)
#check SimplicialObject.eilenbergMacLane.skeleton.objIso.hom_naturality
#check SimplicialObject.eilenbergMacLane.skeleton.objIso.inv_naturality
#check (inferInstance : (SimplicialObject.eilenbergMacLane X k).IsSkeletal k)
#check SimplicialObject.IsSkeletal.truncation.homEquiv

end CategoryTheory
