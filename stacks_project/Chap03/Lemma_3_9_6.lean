/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Size
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Cardinal AlgebraicGeometry

/- Lemma 3.9.6. For morphisms of schemes `f : X ⟶ S` and `g : Y ⟶ S`, the size of the fibre
product `pullback f g` is at most `max X.size Y.size`. -/
@[stacks 04T6] #check (AlgebraicGeometry.Scheme.size_pullback_le :
  ∀ {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S),
    (pullback f g).size ≤ max X.size Y.size)

#check (AlgebraicGeometry.Scheme.size_le_of_isPullback :
  ∀ {X Y S P : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {fst : P ⟶ X} {snd : P ⟶ Y}, IsPullback fst snd f g →
    P.size ≤ max X.size Y.size)
