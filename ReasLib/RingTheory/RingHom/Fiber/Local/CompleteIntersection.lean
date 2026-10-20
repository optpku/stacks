module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.Basic
public import ReasLib.RingTheory.RingHom.Fiber.Local

@[expose] public section

/-!
# Complete Intersections of Local Fibers

This leaf owns the complete-intersection condition on the canonical local ring
of the residue-field fiber selected by a target prime.
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The local residue-field fiber of `f` at `q` is a complete intersection over
the residue field of the contracted prime. -/
@[stacks 00SY "complete-intersection local fiber at a prime"]
def Fiber.IsCompleteIntersectionAt (f : R →+* S) (q : PrimeSpectrum S) : Prop :=
  @Algebra.IsCompleteIntersectionOver.{u, max u v}
    (Ideal.comap f q.asIdeal).ResidueField
    (@fiberLocalRingAt R _ S _ f.toAlgebra q)
    inferInstance
    (@fiberLocalRingAtCommRing R _ S _ f.toAlgebra q)
    (@fiberLocalRingAtResidueFieldAlgebra R _ S _ f.toAlgebra q)

end RingHom
