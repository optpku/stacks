/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Definition 33.44.1: for a proper scheme `X` of dimension at most one over a field, the degree
of a finite locally free module `ℰ` of rank `n` is `χ(X, ℰ) - n χ(X, 𝒪_X)`. -/
@[stacks 0AYR] #check
  (AlgebraicGeometry.Scheme.Modules.curveDegree :
    ∀ {k : Type u} [Field k] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
      (hdim : topologicalKrullDim X ≤ 1) (ℰ : X.Modules) (n : ℕ)
      [IsFiniteLocallyFreeOfRank n ℰ], ℤ)

#check AlgebraicGeometry.Scheme.Modules.curveDegree_def

#check AlgebraicGeometry.Scheme.Modules.curveDegree_eq_eulerCharacteristic_sub_structureSheaf_of_invertible
