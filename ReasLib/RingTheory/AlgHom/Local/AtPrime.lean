/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.Local.AtPrime
public import ReasLib.RingTheory.RingHom.Local.Surjective

@[expose] public section

/-!
# Algebra homomorphisms on local rings at a prime

This leaf upgrades the canonical map between local rings induced by a ring
homomorphism to an algebra homomorphism whenever the original map respects a
common base ring.

@stack 07FH
-/

universe u v w

namespace AlgHom

variable {k : Type u} {R : Type v} {S : Type w}
variable [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

/-- The algebra homomorphism between the source and target local rings induced
by an algebra homomorphism at a target prime. -/
@[stacks 07FH "localized algebra map at a prime"]
noncomputable def localAlgHomAt (f : R →ₐ[k] S) (q : PrimeSpectrum S) :
    f.toRingHom.sourceLocalRingAt q →ₐ[k] Localization.AtPrime q.asIdeal :=
  Localization.localAlgHom (Ideal.comap f.toRingHom q.asIdeal) q.asIdeal f rfl

/-- The underlying ring homomorphism of `localAlgHomAt` is the canonical map
between the corresponding local rings. -/
@[stacks 07FH "underlying localized ring map", simp]
theorem localAlgHomAt_toRingHom (f : R →ₐ[k] S) (q : PrimeSpectrum S) :
    (f.localAlgHomAt q).toRingHom = f.toRingHom.localRingHomAt q := rfl

namespace localAlgHomAt

/-- The algebra map on local rings is a local homomorphism on underlying rings. -/
instance instIsLocalHom (f : R →ₐ[k] S) (q : PrimeSpectrum S) :
    IsLocalHom (f.localAlgHomAt q).toRingHom := by
  rw [AlgHom.localAlgHomAt_toRingHom]
  infer_instance

/-- Surjectivity of an algebra map is preserved by passage to the corresponding local rings. -/
theorem surjective (f : R →ₐ[k] S) (hf : Function.Surjective f.toRingHom)
    (q : PrimeSpectrum S) :
    Function.Surjective (f.localAlgHomAt q).toRingHom := by
  rw [AlgHom.localAlgHomAt_toRingHom]
  exact f.toRingHom.localRingHomAt_surjective hf q

/-- The kernel of a surjective algebra map after localization is the localized kernel ideal. -/
theorem ker (f : R →ₐ[k] S) (hf : Function.Surjective f.toRingHom)
    (q : PrimeSpectrum S) :
    RingHom.ker (f.localAlgHomAt q).toRingHom =
      f.toRingHom.localKernelIdealAt q := by
  rw [AlgHom.localAlgHomAt_toRingHom]
  exact f.toRingHom.ker_localRingHomAt hf q

end localAlgHomAt

end AlgHom
