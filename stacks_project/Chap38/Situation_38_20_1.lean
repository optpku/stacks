/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.BaseChange.IsomorphismFunctor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
variable (u : ℱ ⟶ 𝒢) (T : Over S)

/- Situation 38.20.1: the base changes on which `u` is an isomorphism define a
subterminal contravariant functor on schemes over `S`. -/
@[stacks 05MH] #check
  (AlgebraicGeometry.Scheme.Modules.isomorphismFunctor f u : (Over S)ᵒᵖ ⥤ Type u)

#check
  (AlgebraicGeometry.Scheme.Modules.baseChangeMap f T.hom u :
    AlgebraicGeometry.Scheme.Modules.baseChangeModule f T.hom ℱ ⟶
      AlgebraicGeometry.Scheme.Modules.baseChangeModule f T.hom 𝒢)

#check
  (AlgebraicGeometry.Scheme.Modules.isomorphismFunctor_obj_nonempty_iff f u T :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.isomorphismFunctor f u).obj
      (Opposite.op T)) ↔
        IsIso (AlgebraicGeometry.Scheme.Modules.baseChangeMap f T.hom u))

#check
  (AlgebraicGeometry.Scheme.Modules.isomorphismFunctor_obj_isEmpty_iff f u T :
    IsEmpty ((AlgebraicGeometry.Scheme.Modules.isomorphismFunctor f u).obj
      (Opposite.op T)) ↔
        ¬ IsIso (AlgebraicGeometry.Scheme.Modules.baseChangeMap f T.hom u))

#check
  (AlgebraicGeometry.Scheme.Modules.isomorphismFunctorObjSubsingleton f u T :
    Subsingleton ((AlgebraicGeometry.Scheme.Modules.isomorphismFunctor f u).obj
      (Opposite.op T)))

#check (Mono (AlgebraicGeometry.Scheme.Modules.baseChangeMap f T.hom u) : Prop)

#check (Epi (AlgebraicGeometry.Scheme.Modules.baseChangeMap f T.hom u) : Prop)

#check (AlgebraicGeometry.Scheme.Modules.baseChangeMap f T.hom u = 0 : Prop)
