module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
# Support dimension of short exact sequences

The support dimension is a property of modules, independent of the
Hilbert--Samuel construction.  This leaf provides the short-exact-sequence
formula in the namespace of its canonical owner, `Module.supportDim`.
-/

@[expose] public section

universe u v

open CategoryTheory
open CategoryTheory.ShortComplex

namespace Module

/-- Lemma 10.62.7 (0B51): the support dimension of the middle term of a short
exact sequence is the maximum of the support dimensions of its two endpoint modules. -/
@[stacks 0B51 "support dimension of a short exact sequence"]
theorem supportDim_eq_max_of_shortExact
    {R : Type u} [CommRing R]
    {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) :
    supportDim R S.X₂ = max (supportDim R S.X₁) (supportDim R S.X₃) := sorry

/- The support dimension is defined as the order-theoretic Krull dimension of
the support.  Full support therefore identifies it with the ambient spectrum;
this is useful independently of finite generation. -/
/-- Full support identifies a module's support dimension with the Krull dimension of its ring. -/
theorem supportDim_eq_ringKrullDim_of_support_eq_univ
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (hsupp : support R M = Set.univ) :
    supportDim R M = ringKrullDim R := sorry

/- The quotient version packages the support-intersection computation for a
finite module.  It is the reusable owner behind principal-quotient arguments. -/
/-- A full-support finite module has quotient dimension equal to the quotient ring dimension. -/
theorem supportDim_quotient_eq_ringKrullDim_quotient_of_support_eq_univ
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R)
    (hsupp : support R M = Set.univ) :
    supportDim R (M ⧸ (I • (⊤ : Submodule R M))) =
      ringKrullDim (R ⧸ I) := sorry

end Module
