/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart
public import ReasLib.RingTheory.ReesAlgebra.Reduced

/-!
# Reduced affine blowup charts

This leaf records reducedness of the degree-zero homogeneous localization
which defines an affine blowup chart.  The construction and its structural
maps remain owned by `ReesAlgebra.BlowupChart`.
-/

@[expose] public section

universe u

namespace AffineBlowupChart

variable {R : Type u} [CommRing R]

/-- Every affine chart of the blowup of a reduced commutative ring is reduced. -/
@[stacks 052S "reduced affine blowup chart"]
instance instIsReduced (I : Ideal R) [IsReduced R] (a : I) :
    IsReduced (affineBlowupChart I a) := sorry

end AffineBlowupChart
