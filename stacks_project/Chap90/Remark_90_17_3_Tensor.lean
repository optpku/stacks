/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Lifts.Tangent
public import stacks_project.Chap90.«90_17_5_3_SquareZero»
import StacksCheckRecall

/-!
# Tangent-space comparison for residue-fibre lifts along `k[V]`

If `p` satisfies Schlessinger's (S2), then so does the residue slice `F_x0`, the
associated isomorphism-class functor satisfies (H2), and isomorphism classes of
lifts of `x0` along `k[V] ⟶ k` are canonically identified with
`T F_x0 ⊗[k] V` as `k`-vector spaces.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open ArtinianLocalAlgCat
open scoped TensorProduct

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
variable [Functor.HasSchlessingerS2 p] (x0 : p.Fiber (residue Λ k))
variable (V : FGModuleCat.{u} k)

/- Remark 90.17.3: the tangent-tensor comparison remains available through this
historical import, together with the square-zero kernel API. -/
@[stacks 06JG]
#check (CategoryTheory.Functor.liftsSquareZeroLinearEquiv p x0 V :
  Functor.lifts p (squareZeroToResidue Λ k V) x0 ≃ₗ[k]
    (Functor.fiberIsoClassFunctor (Over.forget (Functor.Fiber.fiberInclusion.obj x0) ⋙ p)).obj
      (dualNumber Λ k) ⊗[k] V)
