module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.Finite
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.RingHom.Fiber.Quotient

/-!
# Depth Along Flat Local Maps

@stack 0337
@stack 0338

The depth formulas in this leaf are stated on the canonical closed fiber
`(maximalIdeal R).Fiber S`.  They are independent of the Chapter 10 proof
presentation and form the common base for Cohen--Macaulay and Serre-condition
permanence results.
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct Algebra.TensorProduct.Right

namespace Algebra.Fiber

universe u v w x

/-- For a flat local homomorphism `R → S`, a finite `R`-module `M`, and a finite
`S`-module `N` flat over `R`, the depth of `N ⊗[R] M` is the sum of the depths of
`M` and of its canonical closed-fiber base change. -/
@[stacks 0338]
theorem moduleDepth_tensor_eq_add_closed
    {R : Type u} {S : Type v} {M : Type w} {N : Type x}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Finite S N] [Module.Flat R N] :
    moduleDepth S (N ⊗[R] M) =
      moduleDepth R M +
        moduleDepth ((maximalIdeal R).Fiber S) (((maximalIdeal R).Fiber S) ⊗[S] N) := sorry

/-- For a flat local homomorphism `R → S` of Noetherian local rings, the depth
of `S` is the sum of the depths of `R` and the canonical closed fiber. -/
@[stacks 0337]
theorem moduleDepth_target_eq_add_closed
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S] :
    moduleDepth S S =
      moduleDepth R R + moduleDepth ((maximalIdeal R).Fiber S) ((maximalIdeal R).Fiber S) := sorry

end Algebra.Fiber
