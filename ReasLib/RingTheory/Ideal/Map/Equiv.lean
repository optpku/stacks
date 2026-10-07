module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Transporting ideals across ring equivalences

This file records the small compatibility lemmas needed when a ring equivalence intertwines two
maps from a common base ring. Mathlib's `Ideal.map_isMaximal_of_equiv` remains the canonical
maximal-ideal transport; `Ideal.IsMaximal.map_ringEquiv` exposes it after coercing the equivalence
to a `RingHom`.
-/

@[expose] public section

universe u v w

namespace Ideal

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]

/-- Mapping along a ring equivalence preserves maximality when the map is written explicitly as a
`RingHom`. -/
theorem IsMaximal.map_ringEquiv (e : S ≃+* T) {q : Ideal S} [q.IsMaximal] :
    (q.map e.toRingHom).IsMaximal := sorry

/-- Contracting an ideal after mapping it across a compatible ring equivalence agrees with
contracting the original ideal. -/
theorem map_comap_eq_of_ringEquiv_comp (e : S ≃+* T)
    {f : R →+* S} {g : R →+* T} (he : e.toRingHom.comp f = g) (q : Ideal S) :
    (q.map e.toRingHom).comap g = q.comap f := sorry

/-- A compatible ring equivalence transports an ideal lying over a base ideal to another ideal
lying over the same base ideal. -/
theorem LiesOver.map_ringEquiv [Algebra R S] [Algebra R T]
    (e : S ≃+* T)
    (he : e.toRingHom.comp (algebraMap R S) = algebraMap R T)
    {p : Ideal R} {q : Ideal S} [q.LiesOver p] :
    (q.map e.toRingHom).LiesOver p := sorry

/-- A ring equivalence maps the nilradical onto the nilradical. -/
theorem map_nilradical_of_ringEquiv (e : S ≃+* T) :
    (nilradical S).map e.toRingHom = nilradical T := sorry

end Ideal
