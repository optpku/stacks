module

public import ReasLib.LinearAlgebra.UniversallyInjective
import StacksCheckRecall

@[expose] public section

universe u v w

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Definition 35.4.5: an active `Algebra R S` represents the ring map `R → S`; it is
universally injective when `Algebra.linearMap R S` is universally injective as an `R`-linear map. -/
@[stacks 08WL] #check
  (LinearMap.UniversallyInjective.{u, u, v, w} (Algebra.linearMap R S) : Prop)
