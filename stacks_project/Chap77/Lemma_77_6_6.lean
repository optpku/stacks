/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AssociatedPoints.Relative.Injectivity
import StacksCheckRecall

/-!
# Lemma 77.6.6

If a flat morphism of algebraic spaces over `Y` covers the relative associated
points of a finite-type quasi-coherent module that is flat over `Y`, then the
pullback-pushforward unit is a monomorphism and remains so after any base
change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

namespace relativeAssassin

/- Lemma 77.6.6 (1): A flat morphism covering the relative assassin induces an
injective canonical map from a finite-type quasi-coherent module flat over the base. -/
@[stacks 0CW6] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin.unit_mono_of_subset_range :
    ∀ {S : Scheme.{u}} {Y X X' : AlgebraicSpace S}
      (f : X ⟶ Y) (g : X' ⟶ X) [Flat g] [LocallyOfFiniteType f] (F : X.Modules)
      [F.IsQuasicoherent] [F.IsFiniteType],
      flatOver F f → relativeAssassin f F ⊆ Set.range (Points.map g) →
        Mono ((pullbackPushforwardAdjunction g).unit.app F))

/- Lemma 77.6.6 (2): The canonical map remains injective after every base change. -/
@[stacks 0CW6] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin.unit_mono_afterBaseChange_of_subset_range :
    ∀ {S : Scheme.{u}} {Y X X' : AlgebraicSpace S}
      (f : X ⟶ Y) (g : X' ⟶ X) [Flat g] [LocallyOfFiniteType f] (F : X.Modules)
      [F.IsQuasicoherent] [F.IsFiniteType],
      flatOver F f → relativeAssassin f F ⊆ Set.range (Points.map g) →
        ∀ {Z : AlgebraicSpace S} (h : Z ⟶ Y),
        Mono ((pullbackPushforwardAdjunction
          (Limits.pullback.fst (Limits.pullback.fst f h) g)).unit.app
          ((pullback (Limits.pullback.fst f h)).obj F)))

end relativeAssassin

end AlgebraicGeometry.AlgebraicSpace.Modules
