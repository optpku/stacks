module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange.IsomorphismFunctor
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Opposite

universe u

variable {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
variable (u : ℱ ⟶ 𝒢) (T : SchemeOver B)

-- Source context: injectivity is not preserved by arbitrary base change. Following the scheme
-- analogue, only F_iso is constructed; the other variants are recorded as Mono, Epi, and
-- vanishing conditions on the base-changed map.

/- Situation 77.7.1: the base changes on which `u` is an isomorphism define a
subterminal contravariant functor on schemes over `B`. Injectivity, surjectivity,
and vanishing are recorded as conditions on the base-changed map. -/
@[stacks 083F] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isomorphismFunctor f u :
    (SchemeOver B)ᵒᵖ ⥤ Type u)

#check
  (Modules.baseChangeSpace f T.hom : AlgebraicSpace S)

#check
  (Modules.baseChangeProj f T.hom : Modules.baseChangeSpace f T.hom ⟶ X)

#check
  (Modules.baseChangeMap f T.hom u :
    Modules.baseChangeModule f T.hom ℱ ⟶ Modules.baseChangeModule f T.hom 𝒢)

#check
  (Modules.isomorphismFunctor_obj_nonempty_iff f u T :
    Nonempty ((Modules.isomorphismFunctor f u).obj (op T)) ↔
      IsIso (Modules.baseChangeMap f T.hom u))

#check
  (Modules.isomorphismFunctor_obj_isEmpty_iff f u T :
    IsEmpty ((Modules.isomorphismFunctor f u).obj (op T)) ↔
      ¬ IsIso (Modules.baseChangeMap f T.hom u))

#check
  (Modules.isomorphismFunctorObjSubsingleton f u T :
    Subsingleton ((Modules.isomorphismFunctor f u).obj (op T)))

#check (Mono (Modules.baseChangeMap f T.hom u) : Prop)

#check (Epi (Modules.baseChangeMap f T.hom u) : Prop)

#check (Modules.baseChangeMap f T.hom u = 0 : Prop)
