module

public import ReasLib.RingTheory.KrullDimension.FiniteType.Local
public import ReasLib.RingTheory.KrullDimension.Fiber

@[expose] public section

/-!
# Local dimension under a surjective finite-type presentation

@stack 00P2

The height correction is expressed by `RingHom.primeHeightDefect`, so the
public formula does not depend on a chosen polynomial presentation.
-/

open TopologicalSpace

universe u v w

namespace PrimeSpectrum

/-- Lemma 10.116.4 (00P2): under a surjection of finite-type algebras over a
field, the local dimension at the contracted point is the target local
dimension plus the corresponding prime-height defect. -/
@[stacks 00P2]
theorem topologicalKrullDimAt_comap_eq_add_primeHeightDefect
    {k : Type u} [Field k]
    {S' : Type v} [CommRing S'] [Algebra k S'] [Algebra.FiniteType k S']
    {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (f : S' →ₐ[k] S) (hf : Function.Surjective f) (x : PrimeSpectrum S) :
    topologicalKrullDimAt (PrimeSpectrum.comap f.toRingHom x) =
      topologicalKrullDimAt x +
        (f.toRingHom.primeHeightDefect x : WithBot ℕ∞) := sorry

end PrimeSpectrum
