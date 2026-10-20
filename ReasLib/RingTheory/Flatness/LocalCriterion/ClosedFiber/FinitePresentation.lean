module

public import ReasLib.RingTheory.EssentialFiniteness.Basic
public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.Noetherian

/-!
# The Finitely Presented Closed-Fiber Flatness Criterion

@stack 00R7

This is the approximation-stable form of the closed-fiber criterion.  As in
the Noetherian leaf, a single top-ring module is primitive data and all lower
actions are canonical `RestrictScalars` views.  The two essentially finite
presentation hypotheses remain explicit because they are evidence about the
chosen maps, rather than coherent ambient instances.
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w x

section

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
variable [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
variable [AddCommGroup M] [Module S' M] [Module.FinitePresentation S' M]

namespace Module.Flat.ClosedFiber

/-- A finitely presented top module is flat over the middle ring when the two
base maps are essentially finitely presented, the module is flat over the
base, and its canonical closed-fiber base change is flat. -/
@[stacks 00R7 "module clause"]
theorem of_essFinitePresentation
    (hRS : RingHom.EssFinitePresentation (algebraMap R S))
    (hRS' : RingHom.EssFinitePresentation (algebraMap R S'))
    (h_fiber : Module.Flat ((maximalIdeal R).Fiber S)
      (((maximalIdeal R).Fiber S) ⊗[S] RestrictScalars S S' M))
    (h_base : Module.Flat R (RestrictScalars R S' M)) :
    Module.Flat S (RestrictScalars S S' M) := sorry

end Module.Flat.ClosedFiber

namespace RingHom.Flat.ClosedFiber

/-- A nonzero finitely presented top module satisfying the closed-fiber
criterion detects flatness of the base-to-middle local map. -/
@[stacks 00R7 "ring-map clause"]
theorem of_essFinitePresentation [Nontrivial M]
    (hRS : RingHom.EssFinitePresentation (algebraMap R S))
    (hRS' : RingHom.EssFinitePresentation (algebraMap R S'))
    (h_fiber : Module.Flat ((maximalIdeal R).Fiber S)
      (((maximalIdeal R).Fiber S) ⊗[S] RestrictScalars S S' M))
    (h_base : Module.Flat R (RestrictScalars R S' M)) :
    (algebraMap R S).Flat := sorry

end RingHom.Flat.ClosedFiber

end
