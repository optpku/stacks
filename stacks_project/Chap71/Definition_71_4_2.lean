/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Definition_71_4_2_LocallyNoetherianFibers
import StacksCheckRecall

/-!
# Definition 71.4.2

Local Noetherianity of a fibre of a morphism of algebraic spaces, and of all
fibres of such a morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Definition 71.4.2 (1): the fibre of `f : X ⟶ Y` over `y` in `Points Y` is
locally Noetherian if and only if the equivalent conditions (1), (2), and (3)
of Lemma 71.4.1 hold. -/
@[stacks 0CUX] #check
  (IsLocallyNoetherianFiber :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Points Y → Prop)

/- Definition 71.4.2 (2): the fibres of `f : X ⟶ Y` are locally Noetherian if
and only if this holds for every `y` in `Points Y`. -/
@[stacks 0CUX] #check
  (LocallyNoetherianFibers :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Prop)
