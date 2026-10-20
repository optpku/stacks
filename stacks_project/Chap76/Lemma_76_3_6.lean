/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective.Etale
import StacksCheckRecall

/-!
# Checking universal injectivity after étale base change

A locally finite type morphism of algebraic spaces is universally injective as
soon as every étale base change is injective on underlying point spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Lemma 76.3.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type, and that for
every étale morphism `g : V ⟶ Y` the map `Points.map (pullback.snd f g)` is
injective. Then `f` is universally injective. -/
@[stacks 0AGE] #check
  (AlgebraicGeometry.AlgebraicSpace.UniversallyInjective.of_locallyOfFiniteType_etale_pointsInjective :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f] →
      (∀ {V : AlgebraicSpace S} (g : V ⟶ Y),
        AlgebraicGeometry.AlgebraicSpace.Etale g →
          Function.Injective (AlgebraicGeometry.AlgebraicSpace.Points.map (pullback.snd f g))) →
      AlgebraicGeometry.AlgebraicSpace.UniversallyInjective f)
