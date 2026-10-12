/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.Cech.Nerve.LowDegree
import StacksCheckRecall

/-!
@stack 016E
-/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe v u

namespace CategoryTheory.Arrow

variable {C : Type u} [Category.{v} C] (f : Arrow C)
variable [f.HasCechNerve]

/- Example 14.3.5 (016E) (1): the Cech nerve of a morphism with the required iterated
pullbacks. -/
@[stacks 016E "Example 14.3.5 (1)"]
#check (f.cechNerve : SimplicialObject C)

#check (f.augmentedCechNerve : SimplicialObject.Augmented C)

/- Example 14.3.5 (016E) (2): simplex operators reindex the coordinates of the iterated
pullback. -/
@[stacks 016E "Example 14.3.5 (2)"]
#check (cechNerve.map_π f :
  ∀ {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (i : Fin (m.unop.len + 1)),
    f.cechNerve.map α ≫ cechNerve.π f m i =
      cechNerve.π f n (α.unop.toOrderHom i))

#check (cechNerve.map_base f :
  ∀ {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m),
    f.cechNerve.map α ≫ cechNerve.base f m = cechNerve.base f n)

/- Example 14.3.5 (016E) (3): degree zero is canonically the source of the arrow. -/
@[stacks 016E "Example 14.3.5 (3)"]
#check (cechNerve.degreeZero.iso f :
  f.cechNerve.obj (op ⦋0⦌) ≅ f.left)

/- Example 14.3.5 (016E) (4): degree one, with its two coordinate projections, is the
pullback of the arrow along itself. -/
@[stacks 016E "Example 14.3.5 (4)"]
#check (cechNerve.degreeOne.isLimit f :
  IsLimit (cechNerve.degreeOne.cone f))

/- Example 14.3.5 (016E) (5): the zeroth face is the second projection. -/
@[stacks 016E "Example 14.3.5 (5)"]
#check (cechNerve.degreeOne.face_zero_iso_hom f :
  f.cechNerve.δ (0 : Fin 2) ≫ (cechNerve.degreeZero.iso f).hom =
    cechNerve.degreeOne.snd f)

/- Example 14.3.5 (016E) (6): the first face is the first projection. -/
@[stacks 016E "Example 14.3.5 (6)"]
#check (cechNerve.degreeOne.face_one_iso_hom f :
  f.cechNerve.δ (1 : Fin 2) ≫ (cechNerve.degreeZero.iso f).hom =
    cechNerve.degreeOne.fst f)

/- The inverse degree-zero comparison recovers both face maps from the pullback projections. -/
#check (cechNerve.degreeOne.snd_iso_inv f :
  cechNerve.degreeOne.snd f ≫ (cechNerve.degreeZero.iso f).inv =
    f.cechNerve.δ (0 : Fin 2))
#check (cechNerve.degreeOne.fst_iso_inv f :
  cechNerve.degreeOne.fst f ≫ (cechNerve.degreeZero.iso f).inv =
    f.cechNerve.δ (1 : Fin 2))

/- Example 14.3.5 (016E) (7): the degree-zero degeneracy is diagonal in the first
coordinate. -/
@[stacks 016E "Example 14.3.5 (7)"]
#check (cechNerve.degreeOne.diagonal_fst f :
  cechNerve.degreeOne.diagonal f ≫ cechNerve.degreeOne.fst f = 𝟙 f.left)

/- Example 14.3.5 (016E) (8): the degree-zero degeneracy is diagonal in the second
coordinate. -/
@[stacks 016E "Example 14.3.5 (8)"]
#check (cechNerve.degreeOne.diagonal_snd f :
  cechNerve.degreeOne.diagonal f ≫ cechNerve.degreeOne.snd f = 𝟙 f.left)

end CategoryTheory.Arrow
