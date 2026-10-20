module

public import Mathlib.RingTheory.RingHom.Surjective
public import ReasLib.RingTheory.RingHom.Local.AtPrime

@[expose] public section

/-!
# Local Quotients of Surjective Ring Homomorphisms

This leaf packages the canonical map on local rings induced by a surjective
ring homomorphism, together with its localized kernel and quotient model.  It
is independent of polynomial presentations and therefore serves every
surjective affine presentation.

@stack 09Q3
-/

noncomputable section

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism is a local surjection when it is both local and surjective. -/
@[stacks 09Q3 "local surjection"]
def IsLocalSurjection (f : R →+* S) : Prop :=
  IsLocalHom f ∧ Function.Surjective f

/-- A map is a local surjection exactly when it is local and surjective. -/
@[simp, stacks 09Q3 "local surjection specification"]
theorem isLocalSurjection_iff (f : R →+* S) :
    f.IsLocalSurjection ↔ IsLocalHom f ∧ Function.Surjective f := sorry

namespace IsLocalSurjection

/-- A local and surjective ring homomorphism is a local surjection. -/
theorem of {f : R →+* S} (h_local : IsLocalHom f) (h_surjective : Function.Surjective f) :
    f.IsLocalSurjection := sorry

/-- A surjective homomorphism from a local ring is a local surjection. -/
theorem of_surjective [IsLocalRing R] {f : R →+* S} (hf : Function.Surjective f) :
    f.IsLocalSurjection := sorry

/-- A local surjection is a local ring homomorphism. -/
theorem isLocalHom {f : R →+* S} (hf : f.IsLocalSurjection) :
    IsLocalHom f := sorry

/-- A local surjection is surjective. -/
theorem surjective {f : R →+* S} (hf : f.IsLocalSurjection) :
    Function.Surjective f := sorry

/-- The identity ring homomorphism is a local surjection. -/
theorem id (R : Type u) [CommRing R] : (RingHom.id R).IsLocalSurjection := sorry

/-- A composite of local surjections is a local surjection. -/
theorem comp {T : Type w} [CommRing T] {f : R →+* S} {g : S →+* T}
    (hg : g.IsLocalSurjection) (hf : f.IsLocalSurjection) :
    (g.comp f).IsLocalSurjection := sorry

/-- The target of a local surjection from a local ring is a local ring. -/
theorem isLocalRing [IsLocalRing R] {f : R →+* S} (hf : f.IsLocalSurjection) :
    IsLocalRing S := sorry

end IsLocalSurjection

/-- For a homomorphism from a local ring, being a local surjection is equivalent to being
surjective. -/
@[simp, stacks 09Q3 "local surjection from a local source"]
theorem isLocalSurjection_iff_surjective [IsLocalRing R] (f : R →+* S) :
    f.IsLocalSurjection ↔ Function.Surjective f := sorry

/-- A surjective ring homomorphism remains surjective after localizing at a
target prime and its contraction. -/
theorem localRingHomAt_surjective (f : R →+* S) (hf : Function.Surjective f)
    (q : PrimeSpectrum S) : Function.Surjective (f.localRingHomAt q) := by
  simpa [RingHom.localRingHomAt, RingHom.sourceLocalRingAt,
    PrimeSpectrum.comap_asIdeal] using
    (RingHom.surjectiveOnStalks_of_surjective hf).localRingHom_surjective
      (PrimeSpectrum.comap f q).asIdeal q.asIdeal rfl

/-- The kernel of the local homomorphism induced by a surjective ring
homomorphism is the localized kernel ideal. -/
theorem ker_localRingHomAt (f : R →+* S) (hf : Function.Surjective f)
    (q : PrimeSpectrum S) :
    RingHom.ker (f.localRingHomAt q) = f.localKernelIdealAt q := by
  have hmap :
      Submonoid.map f (PrimeSpectrum.comap f q).asIdeal.primeCompl =
        q.asIdeal.primeCompl := by
    simpa [PrimeSpectrum.comap_asIdeal] using
      q.asIdeal.map_primeCompl_comap_of_surjective f hf
  have hle : (PrimeSpectrum.comap f q).asIdeal.primeCompl ≤
      Submonoid.comap f q.asIdeal.primeCompl :=
    hmap.symm ▸ (PrimeSpectrum.comap f q).asIdeal.primeCompl.le_comap_map
  let gLoc : f.sourceLocalRingAt q →+* Localization.AtPrime q.asIdeal :=
    IsLocalization.map (Localization.AtPrime q.asIdeal) f hle
  have hker : RingHom.ker gLoc =
      (RingHom.ker f).map (algebraMap R (f.sourceLocalRingAt q)) :=
    IsLocalization.ker_map
      (S := f.sourceLocalRingAt q) (Q := Localization.AtPrime q.asIdeal)
      (M := (PrimeSpectrum.comap f q).asIdeal.primeCompl)
      (T := q.asIdeal.primeCompl) (g := f) hmap
  have hloc : gLoc = f.localRingHomAt q := by
    symm
    change Localization.localRingHom
      (PrimeSpectrum.comap f q).asIdeal q.asIdeal f rfl = gLoc
    apply Localization.localRingHom_unique
    intro r
    exact IsLocalization.map_eq hle r
  rw [hloc] at hker
  simpa [RingHom.localKernelIdealAt] using hker

/-- The quotient of a local source ring by the localized kernel of a
surjective homomorphism canonically identifies with the target local ring. -/
noncomputable def localQuotientAt.ringEquiv (f : R →+* S) (hf : Function.Surjective f)
    (q : PrimeSpectrum S) : f.localQuotientAt q ≃+* Localization.AtPrime q.asIdeal :=
  (Ideal.quotientEquivAlgOfEq ℤ (f.ker_localRingHomAt hf q).symm).toRingEquiv.trans
    (RingHom.quotientKerEquivOfSurjective (f.localRingHomAt_surjective hf q))

end RingHom
