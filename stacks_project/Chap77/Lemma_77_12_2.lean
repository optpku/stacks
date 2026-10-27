/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.HomotopyLimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 77.12.2: in Situation 77.12.1, the object
K = Rlim in D_QCoh(𝒪_X) of the stage sheaves ℱ n, equivalently
((DerivedQCoh.inclusion X).rightAdjoint.obj Klim).obj for an ambient
homotopy limit Klim of the pushforwards of ℱ n in D(𝒪_X), lies in
Dᵇ_QCoh(𝒪_X) and has cohomology sheaves only in degrees ≥ 0. -/
@[stacks 0CX5] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.rightAdjoint_homotopyLimit_isBounded : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (F : SequentialInverseSystem (QCoh X)) (K : ModuleDerived X)
    (hK : HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion X ⋙ DerivedCategory.singleFunctor (Modules X) (0 : ℤ)) K),
    ((DerivedQCoh.inclusion X).rightAdjoint.obj K).obj.IsGE 0 ∧
      DerivedCategory.IsBoundedAbove ((DerivedQCoh.inclusion X).rightAdjoint.obj K).obj)
