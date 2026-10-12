/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Regularity
public import ReasLib.RingTheory.Sequence.QuasiRegular.Regularity
public import ReasLib.RingTheory.Sequence.QuasiRegular.Comparison

/-!
# Implications between regularity conditions for ideal sheaves

Regular ideal sheaves are Koszul-regular, Koszul-regular ideal sheaves are
`H₁`-regular, and `H₁`-regular ideal sheaves are quasi-regular.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

namespace IsRegularIdealSheaf

/-- A regular ideal sheaf is Koszul-regular. -/
@[instance]
theorem isKoszulRegular
    (I : CategoryTheory.Subobject (SheafOfModules.unit X.ringCatSheaf))
    [IsRegularIdealSheaf I] :
    IsKoszulRegularIdealSheaf I := sorry

end IsRegularIdealSheaf

namespace IsKoszulRegularIdealSheaf

/-- A Koszul-regular ideal sheaf is `H₁`-regular. -/
@[instance]
theorem isH1Regular
    (I : CategoryTheory.Subobject (SheafOfModules.unit X.ringCatSheaf))
    [IsKoszulRegularIdealSheaf I] :
    IsH1RegularIdealSheaf I := sorry

end IsKoszulRegularIdealSheaf

namespace IsH1RegularIdealSheaf

/-- An `H₁`-regular ideal sheaf is quasi-regular. -/
@[instance]
theorem isQuasiRegular
    (I : CategoryTheory.Subobject (SheafOfModules.unit X.ringCatSheaf))
    [IsH1RegularIdealSheaf I] :
    IsQuasiRegularIdealSheaf I := sorry

end IsH1RegularIdealSheaf

end AlgebraicGeometry.RingedSpace
