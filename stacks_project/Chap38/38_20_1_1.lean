/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.BaseChange.IsomorphismFunctor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u

variable {S X : Scheme.{u}} (f : X ⟶ S)
variable (ℱ 𝒢 : X.Modules) [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
variable (u : ℱ ⟶ 𝒢) (T : Over S)

/- 38.20.1.1: the contravariant functor on schemes over `S` is singleton precisely where
the base change of `u` is an isomorphism, and empty otherwise. -/
@[stacks 05MI] #check
  (AlgebraicGeometry.Scheme.Modules.isomorphismFunctor f u : (Over S)ᵒᵖ ⥤ Type u)

#check
  (AlgebraicGeometry.Scheme.Modules.isomorphismFunctor_obj_nonempty_iff f u T :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.isomorphismFunctor f u).obj (op T)) ↔
      IsIso (AlgebraicGeometry.Scheme.Modules.baseChangeMap f T.hom u))

#check
  (AlgebraicGeometry.Scheme.Modules.isomorphismFunctor_obj_isEmpty_iff f u T :
    IsEmpty ((AlgebraicGeometry.Scheme.Modules.isomorphismFunctor f u).obj (op T)) ↔
      ¬ IsIso (AlgebraicGeometry.Scheme.Modules.baseChangeMap f T.hom u))
