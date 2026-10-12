/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CompleteIntersection.OverField
public import ReasLib.RingTheory.RingHom.Fiber.Map

@[expose] public section

/-!
# Complete-Intersection Fibers of Ring Homomorphisms

This leaf combines the canonical residue-field algebra carried by `RingHom.Fiber` with the
local-on-the-spectrum complete-intersection predicate over a field.
-/

universe u v

namespace RingHom.Fiber

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The fiber of `f` at `p` is locally a complete intersection over the residue field of `p`. -/
@[stacks 00SL "local complete-intersection fiber at a prime"]
def IsLocalCompleteIntersection (f : R →+* S) (p : Ideal R) [p.IsPrime] : Prop :=
  @_root_.IsLocalCompleteIntersection p.ResidueField (f.Fiber p) inferInstance inferInstance
    (residueFieldAlgebra f p)

/-- The fiber of `f` at `p` is a global complete intersection over the residue field of `p`. -/
def IsGlobalCompleteIntersection (f : R →+* S) (p : Ideal R) [p.IsPrime] : Prop :=
  @_root_.IsGlobalCompleteIntersection p.ResidueField (f.Fiber p) inferInstance inferInstance
    (residueFieldAlgebra f p)

/-- The global complete-intersection condition on a ring-map fiber unfolds to the corresponding
global condition for its residue-field algebra. -/
theorem isGlobalCompleteIntersection_iff (f : R →+* S) (p : Ideal R) [p.IsPrime] :
    IsGlobalCompleteIntersection f p ↔
      @_root_.IsGlobalCompleteIntersection p.ResidueField (f.Fiber p) inferInstance inferInstance
        (residueFieldAlgebra f p) := sorry

end RingHom.Fiber
