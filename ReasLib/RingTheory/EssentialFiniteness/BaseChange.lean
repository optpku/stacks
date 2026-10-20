module

public import ReasLib.RingTheory.Algebra.TensorProduct.FinitePresentation
public import ReasLib.RingTheory.EssentialFiniteness.Basic

/-!
# Base Change for Essential Finite Presentation

The generic right-oriented tensor-product map lives in
`ReasLib.RingTheory.Algebra.TensorProduct.RightMap`. This leaf packages its
finite-presentation and localization consequences into the essential
finite-presentation base-change instance.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- Essential finite presentation is preserved under base change. -/
instance EssFinitePresentation.baseChange (T : Type w) [CommRing T] [Algebra R T]
    [EssFinitePresentation R S] : EssFinitePresentation T (T ⊗[R] S) := sorry

end Algebra
