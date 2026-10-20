/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Affine
import stacks_project.Chap36.Lemma_36_4_1

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.5.2: derived pushforward along an affine morphism of schemes reflects
isomorphisms. -/
@[stacks 08I8] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn.reflectsIsomorphisms_of_isAffineHom :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f],
      (pushforward f).ReflectsIsomorphisms)

end AlgebraicGeometry.Scheme.DerivedQCoh
