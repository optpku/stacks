module

public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.RingTheory.CompleteIntersection.Basic
public import ReasLib.RingTheory.RegularLocalRing.Fiber
public import ReasLib.RingTheory.RingHom.Flat.FaithfullyFlat
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Complete intersections in flat quotient squares

@stack 02JP

This leaf records descent of regular-sequence generation through a flat local square of quotient
maps.  The map into the closed fiber is explicit, avoiding a global or local tensor-product
algebra instance.
-/

open IsLocalRing
open scoped TensorProduct

universe u v

namespace Ideal.IsGeneratedByRegularSequence

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsRegularLocalRing R] [Module.Flat R S] [IsNoetherianRing S]

/-- Lemma 10.135.12: in a flat local square of quotient maps with regular source and closed fiber,
regular-sequence generation of the target kernel and its closed-fiber image descends to the source
kernel. -/
@[stacks 02JP "regular-sequence descent through a flat quotient square"]
theorem of_flat_local_quotientSquare_of_regular_fiber
    (I : Ideal R) (J : Ideal S) (hIJ : I ≤ Ideal.comap (algebraMap R S) J)
    (hclosedFiber : IsRegularLocalRing ((maximalIdeal R).Fiber S))
    (hJ : J.IsGeneratedByRegularSequence)
    (hJbar :
      (Ideal.map
        (Algebra.TensorProduct.includeRight : S →ₐ[R] (maximalIdeal R).Fiber S).toRingHom J).IsGeneratedByRegularSequence)
    (hflatAB : (Ideal.quotientMap J (algebraMap R S) hIJ).Flat) :
    I.IsGeneratedByRegularSequence := sorry

end Ideal.IsGeneratedByRegularSequence
