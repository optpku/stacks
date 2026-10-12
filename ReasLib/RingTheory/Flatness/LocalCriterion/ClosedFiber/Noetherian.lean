/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

/-!
# The Noetherian Closed-Fiber Flatness Criterion

@stack 00MP

This leaf owns the Noetherian form of the local flatness criterion.  The module
is given only over the top ring; its middle- and base-ring structures are the
canonical `RestrictScalars` views.  Thus the API does not ask consumers to
supply three compatible module structures and three scalar-tower proofs.

The closed fiber is Mathlib's canonical `Ideal.Fiber`.  Its module is written
as the ordinary tensor product using the opt-in right tensor-algebra scope;
no competing algebra structure is registered globally.
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
variable [IsNoetherianRing R] [IsNoetherianRing S] [IsNoetherianRing S']
variable [AddCommGroup M] [Module S' M] [Module.Finite S' M]

namespace Module.Flat.ClosedFiber

/-- A finite module over the top Noetherian local ring is flat over the middle
ring when it is flat over the base and its canonical closed-fiber base change
is flat. -/
@[stacks 00MP "module clause"]
theorem of_noetherian
    (h_fiber : Module.Flat ((maximalIdeal R).Fiber S)
      (((maximalIdeal R).Fiber S) ⊗[S] RestrictScalars S S' M))
    (h_base : Module.Flat R (RestrictScalars R S' M)) :
    Module.Flat S (RestrictScalars S S' M) := sorry

end Module.Flat.ClosedFiber

namespace RingHom.Flat.ClosedFiber

/-- Under the Noetherian closed-fiber criterion, a nonzero finite top module
detects flatness of the local map from the base to the middle ring. -/
@[stacks 00MP "ring-map clause"]
theorem of_noetherian [Nontrivial M]
    (h_fiber : Module.Flat ((maximalIdeal R).Fiber S)
      (((maximalIdeal R).Fiber S) ⊗[S] RestrictScalars S S' M))
    (h_base : Module.Flat R (RestrictScalars R S' M)) :
    (algebraMap R S).Flat := sorry

end RingHom.Flat.ClosedFiber

end
