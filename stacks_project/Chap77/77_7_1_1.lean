module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.IsomorphismFunctor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable (ℱ 𝒢 : X.Modules) [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
variable (u : ℱ ⟶ 𝒢) (T : SchemeOver B)

/- 77.7.1.1: the contravariant functor on schemes over `B` is singleton precisely where
the base change of `u` is an isomorphism, and empty otherwise. -/
@[stacks 083G] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismFunctor f u : (SchemeOver B)ᵒᵖ ⥤ Type u)

#check
  (Modules.isomorphismFunctor_obj_nonempty_iff f u T :
    Nonempty ((Modules.isomorphismFunctor f u).obj (op T)) ↔
      IsIso (Modules.baseChangeMap f T.hom u))

#check
  (Modules.isomorphismFunctor_obj_isEmpty_iff f u T :
    IsEmpty ((Modules.isomorphismFunctor f u).obj (op T)) ↔
      ¬ IsIso (Modules.baseChangeMap f T.hom u))
