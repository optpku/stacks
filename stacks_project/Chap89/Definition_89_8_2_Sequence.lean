/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.NormalizedSequence

@[expose] public section

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowupSequence :
  ∀ {S : Scheme.{u}}, AlgebraicSpace S → AlgebraicSpace S → Type (u + 1))
