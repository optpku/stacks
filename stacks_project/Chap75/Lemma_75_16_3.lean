/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Support.Perfect.Compact
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory TopologicalSpace

universe u

/- Lemma 75.16.3 -/
@[stacks 0AED] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.isCompactObject_iff_isPerfect :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (T : Closeds (Points X)),
      IsCompact (T.compl : Set (Points X)) →
        ∀ (E : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn X (T : Set (Points X))),
          IsCompactObject E ↔ ModuleDerived.IsPerfect E.obj)
