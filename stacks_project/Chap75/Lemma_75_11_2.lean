/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 75.11.2. For a quasi-compact, quasi-separated, flat morphism of algebraic
spaces, derived pushforward commutes with the derived coherator up to natural
isomorphism. -/
@[stacks 08GZ] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.Derived.pushforwardCoherator_isomorphic :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f] [Flat f],
      IsIsomorphic (Modules.moduleDerivedPushforward f ⋙ QCoh.Derived.coherator Y)
        (QCoh.Derived.coherator X ⋙ QCoh.Derived.pushforward f))
