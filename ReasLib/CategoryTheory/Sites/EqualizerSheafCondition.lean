/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition

@[expose] public section

noncomputable section

universe t w v u

namespace CategoryTheory.Equalizer.Presieve.Arrows

open CategoryTheory.Limits Opposite

variable {C : Type u} [Category.{v} C]
variable (P : Cᵒᵖ ⥤ Type w)
variable {B : C} {I : Type t} [Small.{w} I]
variable (X : I → C) (π : (i : I) → X i ⟶ B)
variable [(Presieve.ofArrows X π).HasPairwisePullbacks]

/-- The restriction fork associated with an indexed family of arrows into a common object. -/
def fork : Fork (firstMap P X π) (secondMap P X π) :=
  Fork.ofι (forkMap P X π) (w P X π)

end CategoryTheory.Equalizer.Presieve.Arrows
