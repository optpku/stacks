/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.GradedAlgebra.Hull
import StacksCheckRecall

/-!
# Hulls of isomorphism classes of graded-algebra deformations

In the classical case, if `P` is a finitely generated graded `k`-algebra, the
set-valued functor of isomorphism classes of objects of `Def_P` admits a hull.
-/

@[expose] public section

open CategoryTheory Functor

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (Λ)

/- Lemma 93.7.4
The functor of isomorphism classes of deformations of a finitely generated,
locally finite graded algebra over a classical complete local base has a hull.
-/
@[stacks 0ET3] #check (FiniteProjectiveGradedAlgebraCat.exists_isHull_isoClass Λ :
  ∀ (P : FiniteProjectiveGradedAlgebra k) [Algebra.FiniteType k P.carrier]
    [ArtinianLocalAlgCat.IsClassical Λ k],
    ∃ ξ : FormalObject (CategoryTheory.Functor.isoClassProjection
      (FiniteProjectiveGradedAlgebraCat.deformationForgetULift Λ P)),
      FormalObject.IsHull ξ)
