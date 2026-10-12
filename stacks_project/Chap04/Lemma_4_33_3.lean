/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.StronglyCartesian
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Functor

universe uA uB uC vA vB vC

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable (F : A ⥤ B) (G : B ⥤ C) {a b : A} (φ : a ⟶ b)
variable [F.IsStronglyCartesian (F.map φ) φ]
variable [G.IsStronglyCartesian (G.map (F.map φ)) (F.map φ)]

/- Lemma 4.33.3: strong cartesianness is preserved when a morphism and its image are strongly
cartesian for two successive functors. -/
@[stacks 09WU]
#check (isStronglyCartesian_map_comp F G φ :
  (F ⋙ G).IsStronglyCartesian ((F ⋙ G).map φ) φ)

end CategoryTheory.Functor
