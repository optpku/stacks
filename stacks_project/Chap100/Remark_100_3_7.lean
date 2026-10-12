/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.HomotopyCategory.LocallyGroupoidal
public import stacks_project.Chap100.Remark_100_3_7_SpacesOver
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Remark 100.3.7 (1): for an algebraic stack `Y`, `SpacesOver Y` is the
2-category of morphisms `f : X ⟶ Y` of algebraic stacks representable by
algebraic spaces, with 1-morphisms `(g, β : f1 ⟶ g ≫ f2)` and 2-morphisms
`α : g ⟶ g'` satisfying `β ≫ (α ▷ f2) = β'`. -/
@[stacks 04ZQ] #check SpacesOver

/- Remark 100.3.7 (2): the hom-categories of `SpacesOver Y` are setoids, i.e.
`IsGroupoid` plus `Quiver.IsThin`: 2-morphisms are invertible by
`SpacesOver.locallyGroupoid`, and unique when they exist by
`SpacesOver.homIsThin` from faithfulness of the target structural morphism. -/
@[stacks 04ZQ] #check @SpacesOver.homIsThin
@[stacks 04ZQ] #check @SpacesOver.locallyGroupoid

/- Remark 100.3.7 (3): replacing 1-morphisms of `SpacesOver Y` by isomorphism
classes yields a 1-category, namely `Bicategory.HomotopyCategory (SpacesOver Y)`;
with the locally groupoidal instance, those isomorphism classes are identified
by `HomotopyCategory.mkHom.eq_iff_isomorphic`. -/
@[stacks 04ZQ] #check
  fun {S : Scheme.{u}} (Y : GroupoidsOver S) [AlgebraicStack Y] ↦
    Bicategory.HomotopyCategory (SpacesOver Y)
@[stacks 04ZQ] #check
  fun {S : Scheme.{u}} (Y : GroupoidsOver S) [AlgebraicStack Y]
      {P Q : SpacesOver Y} {f g : P ⟶ Q} ↦
    (Bicategory.HomotopyCategory.mkHom.eq_iff_isomorphic :
      Bicategory.HomotopyCategory.mkHom f =
          Bicategory.HomotopyCategory.mkHom g ↔ IsIsomorphic f g)

