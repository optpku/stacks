/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.Homology
public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth.Locality
public import ReasLib.RingTheory.Smooth.FormallySmooth.Criteria
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormallySmooth

/-- A scheme morphism is formally smooth exactly when its degree `-1` naive-cotangent
homology is zero and its relative differentials are locally projective. -/
@[stacks 0D0L]
theorem iff_naiveCotangent {X Y : Scheme.{u}} (f : X ⟶ Y) :
    FormallySmooth f ↔
      IsZero ((NL[f.toShHom]).homology (-1)) ∧
        Scheme.Modules.IsLocallyProjective Ω[f.toShHom] := sorry

end AlgebraicGeometry.FormallySmooth
