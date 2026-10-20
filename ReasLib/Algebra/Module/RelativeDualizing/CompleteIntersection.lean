/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.PicardGroup
public import ReasLib.Algebra.Module.RelativeDualizing
public import ReasLib.RingTheory.CompleteIntersection.OverField
public import ReasLib.RingTheory.Gorenstein.CompleteIntersection

@[expose] public section

universe u v

namespace Algebra.DualModule

/-- The dual module of a zero-dimensional global complete intersection over a field is
invertible over the algebra. -/
instance instInvertibleOfGlobalCompleteIntersection
    (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B] [Nontrivial B]
    [IsGlobalCompleteIntersection k B] [Ring.KrullDimLE 0 B] :
    Module.Invertible B (Algebra.DualModule.of k B) := sorry

end Algebra.DualModule
