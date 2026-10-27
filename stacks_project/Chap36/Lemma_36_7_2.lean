/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 36.7.2. For a quasi-compact, quasi-separated, flat morphism `f : X ⟶ Y`,
ambient derived pushforward followed by `RQ_Y` is naturally isomorphic to `RQ_X` followed by
the right-derived quasicoherent pushforward `Φ`. -/
@[stacks 08D8] #check
  (AlgebraicGeometry.Scheme.QCoh.Derived.pushforwardCoherator_isomorphic :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f] [Flat f],
      IsIsomorphic
        (RingedSpace.moduleDerivedPushforward f.toShHom ⋙ Scheme.QCoh.Derived.coherator Y)
        (Scheme.QCoh.Derived.coherator X ⋙ Scheme.QCoh.Derived.pushforward f))
