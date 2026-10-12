/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent.BaseChange

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

#check
  (AlgebraicGeometry.PseudoCoherent.instIsStableUnderBaseChangeAlong :
    ∀ {S' S : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S) [AlgebraicGeometry.Flat g],
      CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAlong
        (@AlgebraicGeometry.PseudoCoherent.{u}) g)

#check
  (AlgebraicGeometry.PseudoCoherent.pullback_snd :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
      [AlgebraicGeometry.PseudoCoherent f] [AlgebraicGeometry.Flat g],
      AlgebraicGeometry.PseudoCoherent (pullback.snd f g))
