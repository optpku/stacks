/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.Minimality
public import ReasLib.AlgebraicGeometry.NumericalType.PicardContraction

namespace NumericalType

/-- A numerical type of nonpositive genus has Picard group additively equivalent to the integers. -/
public theorem existsIntAddEquivPicardGroup_of_genus_le_zero
    (T : NumericalType) (hgenus : T.genus ≤ 0) :
    Nonempty (ℤ ≃+ T.PicardGroup) := sorry

end NumericalType
