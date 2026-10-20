/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Normalized

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.NormalizedBlowup

/-- The source of a normalized blowup of a Nagata scheme at a closed point is normal. -/
theorem source_isNormal {X : Scheme.{u}} [Scheme.Nagata X] (s : Scheme.NormalizedBlowup X) :
    s.source.isNormal := sorry

/-- The source of a normalized blowup of a Nagata scheme at a closed point is Nagata. -/
theorem source_isNagata {X : Scheme.{u}} [Scheme.Nagata X] (s : Scheme.NormalizedBlowup X) :
    Scheme.Nagata s.source := sorry

/-- The normalized blowup morphism of a Nagata scheme at a closed point is proper. -/
theorem hom_isProper {X : Scheme.{u}} [Scheme.Nagata X] (s : Scheme.NormalizedBlowup X) :
    IsProper s.hom := sorry

end AlgebraicGeometry.Scheme.NormalizedBlowup
