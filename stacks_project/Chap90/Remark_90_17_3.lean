/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Lifts.Tangent
import StacksCheckRecall

/-!
# Lift classes of a residue-fibre object along `k[V]`

For a category cofibered in groupoids over `C_Λ`, lifts of a residue-fibre object
along `k[V] ⟶ k` are the isomorphism classes of the localized predeformation
category at that object, and under (S2) they identify with the tangent space of
the slice tensored with `V`.
-/

@[expose] public section

open CategoryTheory
open Functor ArtinianLocalAlgCat
open scoped TensorProduct

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
variable (x0 : p.Fiber (residue Λ k)) (V : FGModuleCat.{u} k)

/- Remark 90.17.3 (1): Let F be a category cofibered in groupoids over
C_Λ. Let x0 be an object of F(k). Let V be a finite-dimensional k-vector
space. Then Lift(x0, k[V]) is the set of isomorphism classes of F_x0(k[V]),
where F_x0 is the predeformation category of objects in F lying over x0.
This is `liftsSquareZeroEquivIsoClass`. -/
@[stacks 06JG]
#check (CategoryTheory.Functor.liftsSquareZeroEquivIsoClass p x0 V :
  lifts p (squareZeroToResidue Λ k V) x0 ≃
    (fiberIsoClassFunctor (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p)).obj
      (squareZero Λ k V))

variable [HasSchlessingerS2 p]

/- Remark 90.17.3 (2): Hence if F satisfies (S2), then so does F_x0, and
Lift(x0, k[V]) = T F_x0 ⊗[k] V as k-vector spaces. This is
`liftsSquareZeroLinearEquiv`. -/
@[stacks 06JG]
#check (CategoryTheory.Functor.liftsSquareZeroLinearEquiv p x0 V :
  lifts p (squareZeroToResidue Λ k V) x0 ≃ₗ[k]
    (fiberIsoClassFunctor (Over.forget (Fiber.fiberInclusion.obj x0) ⋙ p)).obj
      (dualNumber Λ k) ⊗[k] V)
