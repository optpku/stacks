/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Monomorphism

/-!
# Closed immersions and proper monomorphisms

This file gives equivalent characterizations of closed immersions in terms of
properness, universal closedness, monomorphisms, and unramifiedness.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsClosedImmersion

/-- A scheme morphism is a closed immersion exactly when it satisfies any of the six
equivalent combinations of properness or universal closedness with monomorphism,
unramifiedness, universal injectivity, local finite type, and formal unramifiedness. -/
theorem tfae {X S : Scheme.{u}} (f : X ⟶ S) :
    List.TFAE
      [ IsClosedImmersion f
      , IsProper f ∧ Mono f
      , IsProper f ∧ Unramified f ∧ UniversallyInjective f
      , UniversallyClosed f ∧ Unramified f ∧ Mono f
      , UniversallyClosed f ∧ Unramified f ∧ UniversallyInjective f
      , UniversallyClosed f ∧ LocallyOfFiniteType f ∧ Mono f
      , UniversallyClosed f ∧ UniversallyInjective f ∧ LocallyOfFiniteType f ∧
          FormallyUnramified f ] := sorry

end AlgebraicGeometry.IsClosedImmersion
