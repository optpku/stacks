/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Pullback
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 37.59.16: derived pullback along a pseudo-coherent morphism preserves relative
`m`-pseudo-coherence over a locally finite type base morphism. -/
@[stacks 09US] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver.pullback_of_pseudoCoherent :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [PseudoCoherent f] [LocallyOfFiniteType g]
      {E : RingedSpace.ModuleDerived Y.toRingedSpace} {m : ℤ}
      (hE : AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver g E m),
      AlgebraicGeometry.Scheme.ModuleDerived.IsMPseudoCoherentOver (f ≫ g)
        ((RingedSpace.modulePullbackDerived f.toShHom).obj E) m)
