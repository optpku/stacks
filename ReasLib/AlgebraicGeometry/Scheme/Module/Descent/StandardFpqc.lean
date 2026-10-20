/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.Canonical
public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardFpqc.Presentation

/-!
# Descent along standard fpqc covers

Quasi-coherent modules satisfy effective descent along finite affine flat
families whose images jointly cover an affine scheme.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.QCoh.StandardFpqcCover

variable {S : Scheme.{u}}

namespace canonicalFunctor

/-- The canonical functor to quasi-coherent descent data along a standard fpqc
cover is fully faithful. -/
theorem fullyFaithful (𝒰 : AlgebraicGeometry.StandardFpqcCover S) :
    Nonempty (QCoh.canonicalFunctor 𝒰.U 𝒰.map).FullyFaithful := sorry

end canonicalFunctor

namespace DescentData

/-- Every quasi-coherent descent datum along a standard fpqc cover is effective. -/
theorem isEffective (𝒰 : AlgebraicGeometry.StandardFpqcCover S)
    (D : QCoh.DescentData 𝒰.U 𝒰.map) : D.IsEffective := sorry

end DescentData

end AlgebraicGeometry.Scheme.QCoh.StandardFpqcCover
