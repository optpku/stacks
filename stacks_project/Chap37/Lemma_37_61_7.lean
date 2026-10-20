/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Perfect
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.61.7 (1): A regular immersion of schemes is perfect. -/
@[stacks 068C] #check
  (AlgebraicGeometry.IsRegularImmersion.isPerfect :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsRegularImmersion i],
      LocallyOfType RingHom.IsPerfectRingMap i)

/- Lemma 37.61.7 (2): A Koszul-regular immersion of schemes is perfect. -/
@[stacks 068C] #check
  (AlgebraicGeometry.IsKoszulRegularImmersion.isPerfect :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsKoszulRegularImmersion i],
      LocallyOfType RingHom.IsPerfectRingMap i)
