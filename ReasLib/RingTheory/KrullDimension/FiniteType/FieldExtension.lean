module

public import ReasLib.RingTheory.Algebra.TensorProduct.Flat
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra
public import ReasLib.RingTheory.KrullDimension.FiniteType.Local
public import ReasLib.RingTheory.KrullDimension.GoingDown
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Local dimension after a field extension

@stack 00P4
@stack 0CWE

This leaf records invariance of local topological dimension at corresponding
points after extending the ground field of a finite-type algebra, together
with the corresponding fiber-local dimension formulas.
-/

open scoped TensorProduct Algebra.TensorProduct.Right

universe u v w

namespace Algebra.FiniteType

/-- Lemma 10.116.6 (00P4): local dimension is preserved at corresponding
points after extending the ground field of a finite-type algebra. -/
@[stacks 00P4]
theorem topologicalKrullDimAt_eq_of_tensorProduct_fieldExtension
    {k : Type u} [Field k]
    {K : Type v} [Field K] [Algebra k K]
    {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (x : PrimeSpectrum S) (xK : PrimeSpectrum (K ⊗[k] S))
    (hxK : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom xK = x) :
    topologicalKrullDimAt x = topologicalKrullDimAt xK := sorry

/-- Lemma 10.116.7 (1): at corresponding points after a field extension, the fiber-local
dimension plus the source-local dimension equals the target-local dimension. -/
@[stacks 0CWE "(1), local-dimension formula"]
theorem fiberLocalRingAt_add_krullDim_eq
    {k : Type u} [Field k]
    {K : Type v} [Field K] [Algebra k K]
    {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (x : PrimeSpectrum S) (xK : PrimeSpectrum (K ⊗[k] S))
    (hxK : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom xK = x) :
    ringKrullDim (fiberLocalRingAt S (K ⊗[k] S) xK) +
        ringKrullDim (Localization.AtPrime x.asIdeal) =
      ringKrullDim (Localization.AtPrime xK.asIdeal) := sorry

/-- Lemma 10.116.7 (2): the fiber-local dimension plus the residue-field transcendence degree
over the extended field equals the original residue-field transcendence degree. -/
@[stacks 0CWE "(2), residue-transcendence formula"]
theorem fiberLocalRingAt_add_trdeg_eq
    {k : Type u} [Field k]
    {K : Type v} [Field K] [Algebra k K]
    {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (x : PrimeSpectrum S) (xK : PrimeSpectrum (K ⊗[k] S))
    (hxK : PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom xK = x) :
    ringKrullDim (fiberLocalRingAt S (K ⊗[k] S) xK) +
        Cardinal.toNat (Algebra.trdeg K xK.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField) := sorry

/-- Lemma 10.116.7 (3): every point has a point above it after extending the ground field whose
fiber-local dimension is zero. -/
@[stacks 0CWE "(3), zero-dimensional fiber point"]
theorem exists_fiberLocalRingAt_krullDim_eq_zero
    {k : Type u} [Field k]
    {K : Type v} [Field K] [Algebra k K]
    {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (x : PrimeSpectrum S) :
    ∃ xK : PrimeSpectrum (K ⊗[k] S),
      PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom xK = x ∧
        ringKrullDim (fiberLocalRingAt S (K ⊗[k] S) xK) = 0 := sorry

end Algebra.FiniteType
