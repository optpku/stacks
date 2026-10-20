/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.Coproduct
public import stacks_project.Chap48.Lemma_48_3_1_Instances
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 48.13.1 -/
@[stacks 0A9R] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjoint_preservesCoproducts_of_perfect_proper :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [IsNoetherian X] [IsNoetherian Y] [IsProper f]
      [LocallyOfType RingHom.IsPerfectRingMap f]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a) (I : Type u),
      PreservesColimitsOfShape (Discrete I) a)

end AlgebraicGeometry.Scheme.DerivedQCoh
