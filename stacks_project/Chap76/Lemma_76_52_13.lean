/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative.Fiber
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

universe u

/- Lemma 76.52.13: a pseudo-coherent derived module on an algebraic space flat and locally
of finite presentation over a scheme is relatively perfect if and only if it and its derived
pullbacks to every scheme-theoretic fibre are locally bounded below. -/
@[stacks 0GFK] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.isPerfectRelativeTo_iff_locallyBoundedBelow_and_fiber :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [Flat (SchemeRealization.toBase X)]
      [LocallyOfFinitePresentation (SchemeRealization.toBase X)]
      (E : ModuleDerived X) (hE : IsPseudoCoherent X E),
      IsPerfectRelativeTo (SchemeRealization.toBase X) E ↔
        IsLocallyBoundedBelow E ∧
          ∀ s : S, IsLocallyBoundedBelow
            ((pullback (fiberι (SchemeRealization.toBase X) s)).obj E))
