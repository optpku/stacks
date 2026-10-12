/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.QuasiAffine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Normal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent of quasi-affineness along finite surjections

This file owns the standard applications of finite-morphism norms to descent of
quasi-affineness.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IsQuasiAffine

/-- Quasi-affineness descends along finite locally free surjective morphisms. -/
@[stacks 0BD5]
theorem target_of_isFiniteLocallyFree_surjective
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFiniteLocallyFree π] [Surjective π]
    (hX : X.IsQuasiAffine) :
    Y.IsQuasiAffine := sorry

/-- Quasi-affineness descends along a finite surjection to an integral normal scheme. -/
@[stacks 0BD5]
theorem target_of_isFinite_surjective_isIntegral_isNormal
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral Y]
    (hYnormal : Y.isNormal) (hX : X.IsQuasiAffine) :
    Y.IsQuasiAffine := sorry

end AlgebraicGeometry.Scheme.IsQuasiAffine
