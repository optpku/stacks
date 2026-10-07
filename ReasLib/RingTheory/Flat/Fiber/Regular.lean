module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import ReasLib.RingTheory.EssentialFiniteness.RingHom

/-!
# Regular Elements on Closed Fibers

This leaf owns the regular-element lifting criterion for a flat, essentially
finitely presented local map.  Its primary statement uses the canonical closed
fiber `(maximalIdeal R).Fiber S`; the quotient presentation
`S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)`
is exposed only through a companion bridge.  The target element is mapped by
`Algebra.TensorProduct.includeRight`, so no competing `Algebra S` instance is
required for the tensor-product fiber.

@stack 046Z
-/

@[expose] public section

universe u v

open IsLocalRing

namespace RingHom.EssFinitePresentation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]

/-- Lemma 10.128.5: regularity of the image of `f` in the canonical closed fiber of a
flat, essentially finitely presented local map implies both flatness of the principal
quotient and regularity of `f` in the target. -/
@[stacks 046Z "canonical closed-fiber form"]
theorem flat_quotient_and_isRegular_of_closedFiber
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (f : S)
    (hf : IsRegular ((Algebra.TensorProduct.includeRight :
      S →ₐ[R] (maximalIdeal R).Fiber S) f)) :
    Module.Flat R (S ⧸ Ideal.span ({f} : Set S)) ∧ IsRegular f := sorry

/-- The principal quotient remains flat when `f` is regular on the canonical closed fiber. -/
@[stacks 046Z "(1), flat quotient clause"]
theorem flat_quotient_of_closedFiber
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (f : S)
    (hf : IsRegular ((Algebra.TensorProduct.includeRight :
      S →ₐ[R] (maximalIdeal R).Fiber S) f)) :
    Module.Flat R (S ⧸ Ideal.span ({f} : Set S)) := sorry

/-- An element regular on the canonical closed fiber is regular in the target. -/
@[stacks 046Z "(2), regular element clause"]
theorem isRegular_of_closedFiber
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (f : S)
    (hf : IsRegular ((Algebra.TensorProduct.includeRight :
      S →ₐ[R] (maximalIdeal R).Fiber S) f)) :
    IsRegular f := sorry

/-- The source-facing quotient presentation of Lemma 10.128.5.  The canonical
quotient/fiber equivalence is owned by the lower `Ideal.Fiber` layer. -/
@[stacks 046Z "closed-fiber quotient presentation"]
theorem flat_quotient_and_isRegular_of_closedFiberQuotient
    (hess : RingHom.EssFinitePresentation (algebraMap R S)) (f : S)
    (hf : IsRegular
      (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) f)) :
    Module.Flat R (S ⧸ Ideal.span ({f} : Set S)) ∧ IsRegular f := sorry

end RingHom.EssFinitePresentation
