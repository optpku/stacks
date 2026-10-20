module

public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization transport for tensor-product reducedness

This leaf records the localization step independently of minimal-prime or
characteristic assumptions.  It is the support theorem used whenever a tensor product is
localized in one factor.

@stack 030V
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace Algebra.TensorProduct

/-- Reducedness of `S ⊗[R] K` is preserved after localizing the left factor at `M`. -/
@[stacks 030V "localization transport for tensor reducedness"]
theorem isReduced_of_isLocalization_left
    {R : Type u} {S : Type v} {K : Type w} {T : Type x}
    [CommRing R] [CommRing S] [CommSemiring K] [CommRing T]
    [Algebra R S] [Algebra R K] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Module.Flat R K]
    (M : Submonoid S) [IsLocalization M T]
    [IsReduced (S ⊗[R] K)] :
    IsReduced (T ⊗[R] K) := sorry

/-- Explicit-hypothesis form of `isReduced_of_isLocalization_left`; use this bridge when the
source tensor product's reducedness is proposition-valued data rather than an installed instance. -/
@[stacks 030V "explicit localization reducedness bridge"]
theorem isReduced_of_isLocalization_left_of
    {R : Type u} {S : Type v} {K : Type w} {T : Type x}
    [CommRing R] [CommRing S] [CommSemiring K] [CommRing T]
    [Algebra R S] [Algebra R K] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Module.Flat R K]
    (M : Submonoid S) [IsLocalization M T]
    (h : IsReduced (S ⊗[R] K)) :
    IsReduced (T ⊗[R] K) := sorry

end Algebra.TensorProduct
