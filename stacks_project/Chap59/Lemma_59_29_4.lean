/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.EtaleNeighborhood.Cofiltered
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 59.29.4 (1): for a scheme `S` and a geometric point `point : Spec (.of K) ⟶ S`
with `K` algebraically closed, the category of étale neighborhoods is cofiltered. -/
@[stacks 03PQ] #check
  (AlgebraicGeometry.Scheme.GeometricPoint.EtaleNeighborhood.isCofiltered :
    ∀ {S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
      (point : Spec (.of K) ⟶ S),
      IsCofiltered (Scheme.GeometricPoint.EtaleNeighborhoodOf point))

/- Lemma 59.29.4 (2): any two étale neighborhoods of a geometric point admit a third mapping to
both. -/
@[stacks 03PQ] #check
  (AlgebraicGeometry.Scheme.GeometricPoint.EtaleNeighborhood.exists_commonRefinement :
    ∀ {S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
      (point : Spec (.of K) ⟶ S) (U₁ U₂ : Scheme.GeometricPoint.EtaleNeighborhoodOf point),
      ∃ U : Scheme.GeometricPoint.EtaleNeighborhoodOf point,
        Nonempty ((U ⟶ U₁) × (U ⟶ U₂)))

/- Lemma 59.29.4 (3): any two parallel morphisms of étale neighborhoods of a geometric point can
be equalized by a further neighborhood. -/
@[stacks 03PQ] #check
  (AlgebraicGeometry.Scheme.GeometricPoint.EtaleNeighborhood.exists_equalizingRefinement :
    ∀ {S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
      (point : Spec (.of K) ⟶ S) {U U' : Scheme.GeometricPoint.EtaleNeighborhoodOf point}
      (h₁ h₂ : U ⟶ U'),
      ∃ (U'' : Scheme.GeometricPoint.EtaleNeighborhoodOf point) (h : U'' ⟶ U),
        h ≫ h₁ = h ≫ h₂)
