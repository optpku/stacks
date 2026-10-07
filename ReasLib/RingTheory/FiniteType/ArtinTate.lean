module

public import Mathlib.RingTheory.FiniteType
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
@stack 00IS
# Artin--Tate finite-type descent

This leaf packages the finite-type conclusion for an intermediate subalgebra.  The
generator argument is owned by Mathlib's `fg_of_fg_of_fg`; this declaration only converts
the canonical `Subalgebra.FG` conclusion to `Algebra.FiniteType`.
-/

universe u v

namespace Subalgebra

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [Algebra.FiniteType R S]

/- The explicit subalgebra is the mathematical input; `R`, `S`, and the finite-module
   structure are inferable from it and therefore remain implicit/instance parameters. -/
/-- Lemma 10.51.7 (Artin-Tate) (Stacks 00IS): a subalgebra finite in the ambient module of a
finite-type algebra over a Noetherian ring is itself finite type over the base. -/
@[stacks 00IS "Artin--Tate finite-type descent for an intermediate subalgebra"]
theorem finiteType_of_finite (T : Subalgebra R S) [Module.Finite T S] :
    Algebra.FiniteType R T := sorry

end Subalgebra
