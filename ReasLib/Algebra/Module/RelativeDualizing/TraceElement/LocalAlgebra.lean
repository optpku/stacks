/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.TraceElement
public import ReasLib.Algebra.Module.CompositionSeries.Localization
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.FieldRamification
public import Mathlib.FieldTheory.Separable

@[expose] public section

universe u

namespace Algebra

/-- For a finite-dimensional local algebra over a field, the algebra trace, the
canonical relative-dualizing trace element, and the residue-field length
criterion are equivalent. -/
theorem trace_ne_zero_tfae_of_isLocalRing
    (k : Type u) (A : Type u) [Field k] [CommRing A] [Algebra k A]
    [FiniteDimensional k A] [IsLocalRing A] :
    List.TFAE [Algebra.trace k A ≠ 0,
      @Algebra.RelativeDualizingModule.finiteFlatTraceElement k A _ _ _
        (IsNoetherianRing.of_finite k A) _ _ _ ≠ 0,
      Algebra.IsSeparable k (IsLocalRing.ResidueField A) ∧
        DVR.Field.PrimeToChar k (Module.length A A).toNat] := sorry

end Algebra
