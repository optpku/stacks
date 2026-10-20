/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree.Determinant
import StacksCheckRecall

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.44.8 (1): the degree of a finite locally free module on a proper scheme of
dimension at most one equals the degree of its top exterior power. -/
@[stacks 0DJ5] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegree_eq_curveDegree_topExteriorPower :
    ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.IsProper f]
      (hdim : topologicalKrullDim X ≤ 1)
      (ℰ : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank n ℰ],
      AlgebraicGeometry.Scheme.Modules.curveDegree f hdim ℰ n =
        AlgebraicGeometry.Scheme.Modules.curveDegree f hdim (Λ[n] ℰ) 1)

/- Lemma 33.44.8 (2): the top exterior power and determinant sheaf of a finite locally free
module on a proper scheme of dimension at most one have the same degree. -/
@[stacks 0DJ5] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegree_topExteriorPower_eq_curveDegree_determinantSheaf :
    ∀ {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.IsProper f]
      (hdim : topologicalKrullDim X ≤ 1)
      (ℰ : X.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank n ℰ],
      AlgebraicGeometry.Scheme.Modules.curveDegree f hdim (Λ[n] ℰ) 1 =
        AlgebraicGeometry.Scheme.Modules.curveDegree f hdim (det(ℰ)) 1)
