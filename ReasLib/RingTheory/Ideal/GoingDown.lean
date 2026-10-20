module

public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Open spectrum maps and going down

This leaf records the topological open-map criterion for the algebraic going-down property.
-/

@[expose] public section

universe u v

namespace Algebra.HasGoingDown

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A flat algebra over a commutative ring satisfies going down for prime ideals. -/
theorem of_flatModule [Module.Flat R S] : Algebra.HasGoingDown R S :=
  Algebra.HasGoingDown.of_flat

/-- If the canonical map `Spec S → Spec R` is open, then the `R`-algebra `S`
satisfies going down. -/
@[stacks 0407]
theorem of_isOpenMap
    (hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap R S))) :
    Algebra.HasGoingDown R S := sorry

end Algebra.HasGoingDown
