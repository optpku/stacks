/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Norm.Reduction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Normal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent of ample invertible modules along finite surjections

This file owns the standard applications of finite-morphism norms to descent of ample invertible
modules.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule

/-- Ample invertible modules descend along finite locally free surjective morphisms. -/
@[stacks 0BD4]
theorem target_of_isFiniteLocallyFree_surjective
    {X Y : Scheme.{u}} (π : X ⟶ Y) [AlgebraicGeometry.IsFiniteLocallyFree π] [Surjective π]
    (hX : Scheme.Modules.HasAmpleInvertibleModule X) :
    Scheme.Modules.HasAmpleInvertibleModule Y := sorry

/-- Ample invertible modules descend along a finite surjection to an integral normal scheme. -/
@[stacks 0BD4]
theorem target_of_isFinite_surjective_isIntegral_isNormal
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral Y]
    (hYnormal : Y.isNormal) (hX : Scheme.Modules.HasAmpleInvertibleModule X) :
    Scheme.Modules.HasAmpleInvertibleModule Y := sorry

/-- Ample invertible modules descend from the reduction of a Noetherian scheme in prime
characteristic along its identified finite surjection. -/
@[stacks 0BD4]
theorem target_of_isFinite_surjective_isNoetherian_isCharP_isReduction
    {X Y : Scheme.{u}}
    (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsNoetherian Y]
    (p : ℕ) [Fact p.Prime] [Scheme.IsCharP Y p]
    (e : X ≅ Scheme.reduction Y) (hπ : e.hom ≫ Scheme.reductionι Y = π)
    (hX : Scheme.Modules.HasAmpleInvertibleModule X) :
    Scheme.Modules.HasAmpleInvertibleModule Y := sorry

end AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule
