/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Module.IdealDepth
public import ReasLib.RingTheory.Sequence.Regularity.ClosedFiber

@[expose] public section

universe u v

namespace Algebra.Fiber

/-- For a flat local homomorphism of Noetherian local rings with Cohen--Macaulay
closed fiber, the depth of every ideal in the target is bounded below by the
difference of the closed-fiber dimension and the dimension after adjoining the ideal. -/
@[stacks 0BUY]
theorem depth_ge_closedFiberDim_sub_quotientDim
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [Module.CohenMacaulay ((IsLocalRing.maximalIdeal R).Fiber S)
      ((IsLocalRing.maximalIdeal R).Fiber S)] (I : Ideal S) :
    .some (I.depth S) ≥
      WithBot.map₂ (fun d e ↦ d - e)
        (ringKrullDim
          (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)))
        (ringKrullDim
          (S ⧸ (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) ⊔ I))) := sorry

end Algebra.Fiber
