/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.FinitePointSequence

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

#check (AlgebraicGeometry.Scheme.PointBlowupSequence :
  Scheme.{u} → Scheme.{u} → Type (u + 1))

end AlgebraicGeometry.Scheme
