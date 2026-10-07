module

public import ReasLib.Algebra.Module.CompositionSeries.Factor
public import ReasLib.RingTheory.LocalRing.ResidueField.Over

/-!
# Residue degrees of composition factors

This file connects the canonical annihilator point of a composition factor to
the residue-degree API over a local base ring.

@stack 02M0
-/

@[expose] public section

universe u v w

open IsLocalRing

namespace Module.CompositionSeries.Factor

variable {A : Type u} {B : Type v} {M : Type w}
variable [CommRing A] [CommRing B] [IsLocalRing A] [Algebra A B]
variable [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- The base-ring length of a composition factor is the inertia degree of its annihilator point
when the corresponding residue-field map is finite. -/
@[stacks 02M0 "composition-factor length equals inertia degree"]
theorem length_overBase_eq_inertiaDeg
    (s : CompositionSeries (Submodule B M)) (i : Fin s.length)
    (hcomap : Ideal.comap (algebraMap A B) (annihilatorPoint s i).asIdeal = maximalIdeal A)
    (hfinite : (Ideal.ResidueField.mapUnder A (annihilatorPoint s i).asIdeal).Finite) :
    Module.length A (factor s i) =
      ((annihilatorPoint s i).asIdeal.inertiaDeg A : ℕ∞) := sorry

end Module.CompositionSeries.Factor
