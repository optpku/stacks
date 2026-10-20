/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent.Adjunction
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 39.14.4: for a morphism `f : G ⟶ H` of groupoid schemes whose object map is qcqs,
whose target square is cartesian, and whose codomain source and target maps are flat, equivariant
pullback is a left adjoint, equivalently admitting the corresponding pushforward right adjoint. -/
@[stacks 09VH] #check
  (AlgebraicGeometry.GroupoidScheme.QCoh.pullbackOfTargetSquareIsLeftAdjoint :
    ∀ {S : Scheme.{u}} {G H : GroupoidScheme S} (f : GroupoidScheme.Hom G H)
      (_ : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
      [QuasiCompact f.obj.left] [QuasiSeparated f.obj.left]
      [Flat H.s.left] [Flat H.t.left],
      (GroupoidScheme.QCoh.pullback f).IsLeftAdjoint)
