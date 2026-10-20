/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived.FourierMukai.Representability
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.PerfectDerived

universe u

/- Theorem 57.13.3 (Orlov): for a field `k` and smooth proper `k`-schemes `X`, `Y`
with `X` projective over `k`, every `k`-linear fully faithful exact functor
`F : PerfectDerived X ⥤ PerfectDerived Y` is a Fourier–Mukai functor for some
kernel in `D_perf(𝒪_{X ×_k Y})`. -/
@[stacks 0G0C] #check
  (AlgebraicGeometry.SchemeOverField.PerfectDerived.isPerfectFourierMukai_of_fullyFaithful :
    ∀ {k : Type u} [Field k] (X Y : SchemeOverField k)
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom] [Smooth Y.hom]
    [HProjective X.hom]
    (F : PerfectDerived X ⥤ PerfectDerived Y)
    [F.Linear k] [F.Full] [F.Faithful]
    (hF_exact : F.HasTriangulatedStructure),
    IsPerfectFourierMukai F)
