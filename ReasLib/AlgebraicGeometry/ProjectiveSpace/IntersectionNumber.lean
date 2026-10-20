/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Fin.VecNotation
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Proper
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Invertible
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Variety
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Number
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.Whole

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules
open Scheme.Modules.Intersection

/-- Both twisting sheaves in the pair `![𝒪(d), 𝒪(e)]` on the projective plane are invertible. -/
instance instInvertible_twistingSheafPair (k : Type u) [Field k] (d e : ℤ) :
    ∀ j : Fin 2, Invertible (![twistingSheaf k 2 d, twistingSheaf k 2 e] j) := sorry

/-- The intersection number of the twisting sheaves `𝒪(d)` and `𝒪(e)` on the projective
plane over a field equals `d * e`. -/
@[stacks 0GYA]
theorem intersectionNumber_twistingSheaves_eq_mul
    {k : Type u} [Field k] (d e : ℤ)
    [HasExt (Sheaf (Opens.grothendieckTopology
      (⊥ : (scheme k 2).IdealSheafData).subscheme.carrier) AddCommGrpCat.{u})] :
    number k (toSpec k 2) (⊥ : (scheme k 2).IdealSheafData)
      (topologicalKrullDim_bot_eq (scheme k 2) (topologicalKrullDim_scheme_eq k 2))
      ![twistingSheaf k 2 d, twistingSheaf k 2 e] = (d * e : ℚ) := sorry

end AlgebraicGeometry.ProjectiveSpace
