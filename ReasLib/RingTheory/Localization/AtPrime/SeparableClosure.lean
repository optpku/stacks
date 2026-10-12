/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.SeparableClosure.Map
public import ReasLib.RingTheory.Localization.AtPrime.ResidueField
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Separable closures of prime-local residue fields

This leaf applies the map-oriented separable-closure API to the canonical
residue-field map of a prime localization.  The underlying map remains owned
by `Localization.AtPrime.ResidueField` so callers that do not need field
theory avoid this import.

@stack 04GW
-/

universe u v

namespace Localization.AtPrime

/-- If `K` is a separable closure of `κ(p)`, the canonical residue map of
`Rₚ` to `K` is a map-oriented separable closure. -/
@[stacks 04GW "separable closure of a prime-local residue field"]
theorem residueMapOfAlgebra_isSepClosure
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {K : Type v} [Field K] [Algebra p.ResidueField K]
    [IsSepClosure p.ResidueField K] :
    RingHom.IsSepClosure (residueMapOfAlgebra (K := K) p) := sorry

end Localization.AtPrime
