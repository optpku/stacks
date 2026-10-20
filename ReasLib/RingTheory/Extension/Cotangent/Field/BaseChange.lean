/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.Field.Cartier
public import ReasLib.RingTheory.Extension.Cotangent.Field.JacobiZariski
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent comparison under a square of fields

This leaf owns the two canonical base-field comparison maps and the
kernel-cokernel Euler characteristic attached to a commutative square of field
extensions.

@stack 07E3
-/

@[expose] public section

open scoped KaehlerDifferential TensorProduct

noncomputable section

universe u v w x

namespace KaehlerDifferential

/-- The canonical comparison
`K' ⊗[K] Ω[K⁄k] ⟶ Ω[K'⁄k']` for a commutative square of field extensions. -/
@[stacks 07E3 "base-field comparison on differentials"]
noncomputable abbrev baseFieldComparison
    (k : Type u) (k' : Type v) (K : Type w) (K' : Type x)
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k k'] [Algebra k K] [Algebra k K'] [Algebra k' K'] [Algebra K K']
    [IsScalarTower k k' K'] [IsScalarTower k K K'] :
    K' ⊗[K] Ω[K⁄k] →ₗ[K'] Ω[K'⁄k'] :=
  (map k k' K' K').comp (mapBaseChange k K K')

/-- Lemma 15.34.3 (1), tag `07E3`: the kernel of
the comparison on Kaehler differentials is finite-dimensional. -/
@[stacks 07E3 "(1)"]
theorem finiteDimensional_ker_baseFieldComparison
    {k : Type u} {k' : Type v} {K : Type w} {K' : Type x}
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k k'] [Algebra k K] [Algebra k K'] [Algebra k' K'] [Algebra K K']
    [IsScalarTower k k' K'] [IsScalarTower k K K']
    [Algebra.FiniteType k k'] [Algebra.FiniteType K K'] :
    FiniteDimensional K' (LinearMap.ker (baseFieldComparison k k' K K')) := sorry

/-- Lemma 15.34.3 (2), tag `07E3`: the cokernel of
the comparison on Kaehler differentials is finite-dimensional. -/
@[stacks 07E3 "(2)"]
theorem finiteDimensional_cokernel_baseFieldComparison
    {k : Type u} {k' : Type v} {K : Type w} {K' : Type x}
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k k'] [Algebra k K] [Algebra k K'] [Algebra k' K'] [Algebra K K']
    [IsScalarTower k k' K'] [IsScalarTower k K K']
    [Algebra.FiniteType k k'] [Algebra.FiniteType K K'] :
    FiniteDimensional K'
      (Ω[K'⁄k'] ⧸ LinearMap.range (baseFieldComparison k k' K K')) := sorry

end KaehlerDifferential

namespace Algebra.H1Cotangent

/-- The canonical comparison
`K' ⊗[K] H1Cotangent k K ⟶ H1Cotangent k' K'` for a commutative square
of field extensions. -/
@[stacks 07E3 "base-field comparison on first cotangent homology"]
noncomputable abbrev baseFieldComparison
    (k : Type u) (k' : Type v) (K : Type w) (K' : Type x)
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k k'] [Algebra k K] [Algebra k K'] [Algebra k' K'] [Algebra K K']
    [IsScalarTower k k' K'] [IsScalarTower k K K'] :
    K' ⊗[K] H1Cotangent k K →ₗ[K'] H1Cotangent k' K' :=
  (map k k' K' K').comp (LinearMap.liftBaseChange K' (map k k K K'))

/-- Lemma 15.34.3 (3), tag `07E3`: the kernel of
the comparison on first cotangent homology is finite-dimensional. -/
@[stacks 07E3 "(3)"]
theorem finiteDimensional_ker_baseFieldComparison
    {k : Type u} {k' : Type v} {K : Type w} {K' : Type x}
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k k'] [Algebra k K] [Algebra k K'] [Algebra k' K'] [Algebra K K']
    [IsScalarTower k k' K'] [IsScalarTower k K K']
    [Algebra.FiniteType k k'] [Algebra.FiniteType K K'] :
    FiniteDimensional K' (LinearMap.ker (baseFieldComparison k k' K K')) := sorry

/-- Lemma 15.34.3 (4), tag `07E3`: the cokernel of
the comparison on first cotangent homology is finite-dimensional. -/
@[stacks 07E3 "(4)"]
theorem finiteDimensional_cokernel_baseFieldComparison
    {k : Type u} {k' : Type v} {K : Type w} {K' : Type x}
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k k'] [Algebra k K] [Algebra k K'] [Algebra k' K'] [Algebra K K']
    [IsScalarTower k k' K'] [IsScalarTower k K K']
    [Algebra.FiniteType k k'] [Algebra.FiniteType K K'] :
    FiniteDimensional K'
      (H1Cotangent k' K' ⧸ LinearMap.range (baseFieldComparison k k' K K')) := sorry

end Algebra.H1Cotangent

namespace Algebra

/-- Lemma 15.34.3 (5), tag `07E3`: the alternating
kernel-cokernel dimension of the comparison on `Ω` and `H1Cotangent` is the
difference of the two relative transcendence degrees. -/
@[stacks 07E3 "(5)"]
theorem baseFieldComparison_eulerCharacteristic_eq_trdeg_sub_trdeg
    {k : Type u} {k' : Type v} {K : Type w} {K' : Type x}
    [Field k] [Field k'] [Field K] [Field K']
    [Algebra k k'] [Algebra k K] [Algebra k K'] [Algebra k' K'] [Algebra K K']
    [IsScalarTower k k' K'] [IsScalarTower k K K']
    [Algebra.FiniteType k k'] [Algebra.FiniteType K K'] :
    Int.ofNat
          (Module.finrank K'
            (LinearMap.ker (KaehlerDifferential.baseFieldComparison k k' K K'))) -
        Int.ofNat
          (Module.finrank K'
            (Ω[K'⁄k'] ⧸
              LinearMap.range (KaehlerDifferential.baseFieldComparison k k' K K'))) -
        Int.ofNat
          (Module.finrank K'
            (LinearMap.ker (H1Cotangent.baseFieldComparison k k' K K'))) +
        Int.ofNat
          (Module.finrank K'
            (H1Cotangent k' K' ⧸
              LinearMap.range (H1Cotangent.baseFieldComparison k k' K K'))) =
      Int.ofNat (Cardinal.toNat (trdeg k k')) -
        Int.ofNat (Cardinal.toNat (trdeg K K')) := sorry

end Algebra
