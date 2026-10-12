/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.FromZero
public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.Composition.Whiskering
import StacksCheckRecall

@[expose] public section

/-!
@stack 0G5Q

# Lemma 14.33.4 compatibility facade

The zero-simplex extension and its section property are generic facts about augmented simplicial
objects.  Their reusable owners are in `ReasLib`; the chapter contributes no parallel wrappers.
-/

open CategoryTheory
open CategoryTheory.SimplicialObject
open Opposite
open scoped Simplicial

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable (X : SimplicialObject C) {Z : C} (f : Z ⟶ X _⦋0⦌)

/- The canonical map extending a zero-simplex map. -/
@[stacks 0G5Q "Lemma 14.33.4, zero-simplex extension"]
#check (SimplicialObject.fromZero X f :
  (SimplicialObject.const C).obj Z ⟶ X)

variable (Y : SimplicialObject.Augmented C)
variable (s : Y.right ⟶ Y.left _⦋0⦌)
variable (hs : s ≫ Y.hom.app (op ⦋0⦌) = 𝟙 Y.right)

/- Lemma 14.33.4: a zero-simplex section extends to a section of the whole augmentation. -/
@[stacks 0G5Q "Lemma 14.33.4"]
#check (SimplicialObject.fromZero.comp_hom Y s hs :
  SimplicialObject.fromZero Y.left s ≫ Y.hom = 𝟙 _)

variable {Q : SimplicialObject (C ⥤ C)}
variable (F : A ⥤ C) (G : C ⥤ B)
variable (ε : Q ⟶ (SimplicialObject.const (C ⥤ C)).obj (𝟭 C))
variable
  (h₀ : (SimplicialObject.Augmented.whisker F G ε).right ⟶
    (SimplicialObject.Augmented.whisker F G ε).left _⦋0⦌)
  (hh₀ : h₀ ≫ (SimplicialObject.Augmented.whisker F G ε).hom.app (op ⦋0⦌) =
    𝟙 (SimplicialObject.Augmented.whisker F G ε).right)

@[stacks 0G5Q "Lemma 14.33.4 (pre/postcomposition)"]
#check (SimplicialObject.fromZero.comp_hom
    (SimplicialObject.Augmented.whisker F G ε) h₀ hh₀ :
  (SimplicialObject.Augmented.whisker F G ε).left.fromZero h₀ ≫
    (SimplicialObject.Augmented.whisker F G ε).hom = 𝟙 _)

end CategoryTheory
