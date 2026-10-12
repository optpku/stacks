/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.NatTrans.Horizontal
import StacksCheckRecall

@[expose] public section

universe vA uA vB uB vC uC vD uD

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {F₁ F₂ F₃ F₄ : A ⥤ B}
variable {G₁ G₂ G₃ : B ⥤ C}
variable {H₁ H₂ : C ⥤ D}
variable (t : F₁ ⟶ F₂) (t' : F₂ ⟶ F₃) (t'' : F₃ ⟶ F₄)
variable (s : G₁ ⟶ G₂) (s' : G₂ ⟶ G₃) (r : H₁ ⟶ H₂)

/- Lemma 4.28.2 (1): vertical composition is associative. -/
@[stacks 003F "vertical composition is associative"]
#check (Category.assoc t t' t'' : (t ≫ t') ≫ t'' = t ≫ t' ≫ t'')

/- Lemma 4.28.2 (2): horizontal composition is strictly associative. -/
@[stacks 003F "horizontal composition is strictly associative"]
#check (NatTrans.hcomp_assoc t s r : (t ◫ s) ◫ r = t ◫ (s ◫ r))

/- Lemma 4.28.2 (3): identity transformations are left units for vertical composition. -/
@[stacks 003F "identity transformations are left units for vertical composition"]
#check (Category.id_comp t : 𝟙 F₁ ≫ t = t)

/- Lemma 4.28.2 (4): identity transformations are right units for vertical composition. -/
@[stacks 003F "identity transformations are right units for vertical composition"]
#check (Category.comp_id t : t ≫ 𝟙 F₂ = t)

/- Lemma 4.28.2 (5): the identity of an identity functor is a left horizontal unit. -/
@[stacks 003F "identity of the identity functor is a left horizontal unit"]
#check (NatTrans.id_hcomp t : 𝟙 (𝟭 A) ◫ t = t)

/- Lemma 4.28.2 (6): the identity of an identity functor is a right horizontal unit. -/
@[stacks 003F "identity of the identity functor is a right horizontal unit"]
#check (NatTrans.hcomp_id t : t ◫ 𝟙 (𝟭 B) = t)

/- Lemma 4.28.2 (7): horizontal and vertical composition satisfy interchange. -/
@[stacks 003F "horizontal and vertical composition satisfy interchange"]
#check (NatTrans.exchange t t' s s' :
  (t ≫ t') ◫ (s ≫ s') = (t ◫ s) ≫ (t' ◫ s'))

end CategoryTheory
