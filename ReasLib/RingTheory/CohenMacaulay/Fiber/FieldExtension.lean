module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.Noetherian
public import ReasLib.RingTheory.Algebra.TensorProduct.PrimeSpectrum
public import ReasLib.RingTheory.CohenMacaulay.Module.Local

@[expose] public section

/-!
# Cohen--Macaulay Local Rings under Field Extension

This leaf compares the Cohen--Macaulay self-module condition at corresponding primes after
tensoring along a field extension, under either finite-type or essentially-finite-type
hypotheses.
-/

open Algebra.TensorProduct
open scoped TensorProduct

universe u v w

namespace Module.CohenMacaulay.FieldExtension

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {S : Type w} [CommRing S] [Algebra k S]

namespace FiniteType

/- Mathlib cannot register finite-type Noetherianity as an instance because the
base `k` is not recoverable from `S`.  The optional `hS` arguments below default
to the canonical theorem, avoid global instance search, and still permit an
explicit defeq-compatible choice when a downstream construction needs one. -/

/-- Contraction form of the Cohen--Macaulay comparison after extending the ground field of a
finite-type algebra. -/
@[stacks 00RJ "contraction form"]
theorem localizationAtPrime_iff
    [Algebra.FiniteType k S]
    (hS : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S)
    (hT : IsNoetherianRing (K ⊗[k] S) :=
      Algebra.FiniteType.isNoetherianRing_tensor_right (R := k) (Q := K) (T := S))
    (qK : PrimeSpectrum (K ⊗[k] S)) :
    -- Local instance justification (defeq pin): `hS` fixes the Noetherian instance for the contracted localization.
    letI := hS
    -- Local instance justification (defeq pin): `hT` fixes the Noetherian instance for the tensor-product localization.
    letI := hT
    Module.CohenMacaulay
          (Localization.AtPrime (restrictRight qK).asIdeal)
          (Localization.AtPrime (restrictRight qK).asIdeal) ↔
        Module.CohenMacaulay (Localization.AtPrime qK.asIdeal)
          (Localization.AtPrime qK.asIdeal) := sorry

/-- Cohen--Macaulayness at `q : Spec S` is equivalent to Cohen--Macaulayness
at a prime of `Spec(K ⊗[k] S)` lying over `q`. -/
@[stacks 00RJ]
theorem localizationAtPrime_iff_of_liesOver
    [Algebra.FiniteType k S]
    (hS : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S)
    (hT : IsNoetherianRing (K ⊗[k] S) :=
      Algebra.FiniteType.isNoetherianRing_tensor_right (R := k) (Q := K) (T := S))
    (q : PrimeSpectrum S) (qK : PrimeSpectrum (K ⊗[k] S))
    (h_liesOver : restrictRight qK = q) :
    -- Local instance justification (defeq pin): `hS` fixes the Noetherian instance for the source localization.
    letI := hS
    -- Local instance justification (defeq pin): `hT` fixes the Noetherian instance for the tensor-product localization.
    letI := hT
    Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal) ↔
        Module.CohenMacaulay (Localization.AtPrime qK.asIdeal)
          (Localization.AtPrime qK.asIdeal) := sorry

end FiniteType

namespace EssFiniteType

/-- Contraction form of the Cohen--Macaulay comparison for an essentially finite-type field
extension and a Noetherian algebra. -/
@[stacks 045N "contraction form"]
theorem localizationAtPrime_iff
    [Algebra.EssFiniteType k K] [IsNoetherianRing S]
    (hT : IsNoetherianRing (K ⊗[k] S) :=
      Algebra.EssFiniteType.isNoetherianRing_tensor_right (R := k) (Q := K) (T := S))
    (qK : PrimeSpectrum (K ⊗[k] S)) :
    -- Local instance justification (defeq pin): `hT` fixes the Noetherian instance for the tensor-product localization.
    letI := hT
    Module.CohenMacaulay
        (Localization.AtPrime (restrictRight qK).asIdeal)
        (Localization.AtPrime (restrictRight qK).asIdeal) ↔
      Module.CohenMacaulay (Localization.AtPrime qK.asIdeal)
        (Localization.AtPrime qK.asIdeal) := sorry

/-- If `K` is essentially of finite type over `k` and `S` is Noetherian,
Cohen--Macaulayness at `q : Spec S` is equivalent to Cohen--Macaulayness at a
prime of `Spec(K ⊗[k] S)` lying over `q`. -/
@[stacks 045N]
theorem localizationAtPrime_iff_of_liesOver
    [Algebra.EssFiniteType k K] [IsNoetherianRing S]
    (hT : IsNoetherianRing (K ⊗[k] S) :=
      Algebra.EssFiniteType.isNoetherianRing_tensor_right (R := k) (Q := K) (T := S))
    (q : PrimeSpectrum S) (qK : PrimeSpectrum (K ⊗[k] S))
    (h_liesOver : restrictRight qK = q) :
    -- Local instance justification (defeq pin): `hT` fixes the Noetherian instance for the tensor-product localization.
    letI := hT
    Module.CohenMacaulay (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal) ↔
      Module.CohenMacaulay (Localization.AtPrime qK.asIdeal)
        (Localization.AtPrime qK.asIdeal) := sorry

end EssFiniteType

end Module.CohenMacaulay.FieldExtension
