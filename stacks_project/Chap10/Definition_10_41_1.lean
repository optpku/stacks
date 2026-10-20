module

public import Mathlib.Topology.Inseparable
public import Mathlib.RingTheory.Ideal.GoingDown
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.41.1

@stack 00HV
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)

open PrimeSpectrum

/- Definition 10.41.1 (1): a ring map `φ : R →+* S` satisfies going up exactly when the induced
map `Spec(S) → Spec(R)` is a specializing map. -/
@[stacks 00HV "(1)"]
#check (SpecializingMap (comap φ))

/- Definition 10.41.1 (2): after installing the canonical algebra structure from `φ`, the
going-down property is the owner predicate `Algebra.HasGoingDown R S`. -/
@[stacks 00HV "(2)"]
#check (@Algebra.HasGoingDown R S _ _ φ.toAlgebra)

end
