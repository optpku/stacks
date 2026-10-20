/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduced.LocallyNoetherianSingleton
import StacksCheckRecall

/-!
# Reduced locally Noetherian singleton algebraic stacks

An algebraic stack over a scheme is reduced, locally Noetherian, and a
singleton on points if and only if it admits a locally finitely presented,
surjective, flat morphism from the spectrum of a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 100.11.3: An algebraic stack is reduced, locally Noetherian, and has
singleton points if and only if it admits a locally finitely presented,
surjective, flat morphism from the spectrum of a field. -/
@[stacks 06MP] #check
  (AlgebraicGeometry.AlgebraicStack.isReduced_isLocallyNoetherian_subsingleton_points_tfae :
    ∀ {S : Scheme.{u}} (Z : GroupoidsOver S) [AlgebraicStack Z],
      List.TFAE
        [ IsReduced Z ∧ IsLocallyNoetherian Z ∧ Nonempty (Points Z) ∧
            Subsingleton (Points Z)
        , existsLocallyOfFinitePresentationSurjectiveFlatSpecField Z ])

end AlgebraicGeometry.AlgebraicStack
