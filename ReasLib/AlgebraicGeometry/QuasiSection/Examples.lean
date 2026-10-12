/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AffineLine.FpTAway
public import ReasLib.AlgebraicGeometry.QuasiSection.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.GoldenInteger

@[expose] public section

namespace AlgebraicGeometry

namespace GoldenIntegerQuasiSection

/-- The localized affine line over `ℤ` admits a quasi-section given by the golden-integer
finite surjective cover. -/
theorem hasQuasiSection_ambientToSpecInt :
    HasQuasiSection GoldenIntegerQuasiSection.ambientToSpecInt := sorry

end GoldenIntegerQuasiSection

namespace FpTAwayAffineLine

/-- The specified principal open of the affine line over `Polynomial (ZMod p)` admits a
quasi-section. -/
theorem hasQuasiSection_toBase (p : ℕ) [Fact p.Prime] :
    HasQuasiSection (FpTAwayAffineLine.toBase p) := sorry

end FpTAwayAffineLine

end AlgebraicGeometry
