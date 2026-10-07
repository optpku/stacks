module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.NonvanishingOpen

/-!
# Quasi-compact nonvanishing opens of invertible-module sections

On a quasi-compact scheme, the nonvanishing open of a section of any nonnegative tensor power
of an invertible module is quasi-compact.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X : Scheme.{u}}

/-- The nonvanishing open of a global section of a tensor power of an invertible module on a
quasi-compact scheme is compact. -/
theorem isCompact_nonvanishingOpen [CompactSpace X] {L : X.Modules}
    [hL : Invertible L] {n : ℕ}
    (s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤)) :
    IsCompact (hL.nonvanishingOpen s : Set X) := sorry

end AlgebraicGeometry.Scheme.Modules.Invertible
