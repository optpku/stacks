module

public import ReasLib.LinearAlgebra.Trace.GroupAlgebra

/-!
# G-trace of a finite projective group-ring module

The shared group-algebra trace API supplies the identity-coefficient map on
`Λ[G]`, its descent `ε : (Λ[G])♮ →+ Λ♮`, and the G-trace of an endomorphism
of a finite projective left `Λ[G]`-module.
-/

universe u v w

open Ring
open scoped MonoidAlgebra Ring

#check (MonoidAlgebra.coeffOne :
    ∀ {Λ : Type u} {G : Type v} [Ring Λ] [Group G], Λ[G] →+ Λ)

#check (MonoidAlgebra.coeffOne_apply :
    ∀ {Λ : Type u} {G : Type v} [Ring Λ] [Group G] (x : Λ[G]),
    MonoidAlgebra.coeffOne x = x.coeff 1)

#check (MonoidAlgebra.coeffOne_single_one :
    ∀ {Λ : Type u} {G : Type v} [Ring Λ] [Group G] (r : Λ),
    MonoidAlgebra.coeffOne (MonoidAlgebra.single (1 : G) r) = r)

#check (MonoidAlgebra.coeffOne_single_of_ne :
    ∀ {Λ : Type u} {G : Type v} [Ring Λ] [Group G] {g : G} (hg : g ≠ 1) (r : Λ),
    MonoidAlgebra.coeffOne (MonoidAlgebra.single g r) = 0)

#check (MonoidAlgebra.epsilonPre :
    ∀ {Λ : Type u} {G : Type v} [Ring Λ] [Group G], Λ[G] →+ Λ♮)

#check (MonoidAlgebra.epsilonPre_apply :
    ∀ {Λ : Type u} {G : Type v} [Ring Λ] [Group G] (x : Λ[G]),
    MonoidAlgebra.epsilonPre x = CommutatorQuotient.mk (x.coeff 1))

#check (MonoidAlgebra.epsilon :
    ∀ {Λ : Type u} {G : Type v} [Ring Λ] [Group G], (Λ[G])♮ →+ Λ♮)

#check (MonoidAlgebra.epsilon_mk :
    ∀ {Λ : Type u} {G : Type v} [Ring Λ] [Group G] (x : Λ[G]),
    MonoidAlgebra.epsilon (CommutatorQuotient.mk x) = MonoidAlgebra.epsilonPre x)

#check (LinearMap.FiniteProjective.traceG :
    ∀ {Λ : Type u} {G : Type v} [Ring Λ] [Group G]
    {P : Type w} [AddCommGroup P] [Module (Λ[G]) P]
    [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P],
    Module.End (Λ[G]) P →+ Λ♮)

#check (LinearMap.FiniteProjective.traceG_apply :
    ∀ {Λ : Type u} {G : Type v} [Ring Λ] [Group G]
    {P : Type w} [AddCommGroup P] [Module (Λ[G]) P]
    [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P] (f : Module.End (Λ[G]) P),
    LinearMap.FiniteProjective.traceG f = MonoidAlgebra.epsilon
      ((LinearMap.FiniteProjective.traceNatural : Module.End (Λ[G]) P →+ (Λ[G])♮) f))
