module

public import ReasLib.LinearAlgebra.UniversallyInjective

@[expose] public section

universe u v w z

#check (LinearMap.universallyInjective_of_retraction :
  ∀ {R : Type u} [CommRing R] {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (r : N →ₗ[R] M),
    r.comp f = LinearMap.id → LinearMap.UniversallyInjective.{u, v, w, z} f)

#check (RingHom.universallyInjective_algebraMap_of_retraction :
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (rho : S →+* R), rho.comp (algebraMap R S) = RingHom.id R →
      LinearMap.UniversallyInjective.{u, u, v, z} (Algebra.linearMap R S))
