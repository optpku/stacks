/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Hom
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of the ambient Hom equivalence

The local equivalence between stack morphisms and ambient fibred-category morphisms commutes
with postcomposition. This leaf packages that compatibility for reuse by universal constructions.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v w vS

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace StackOver.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y Z : StackOver.{u, v, w, vS} J}

/-- The identity components comparing ambient and bundled postcomposition are natural in stack
`2`-morphisms. -/
private theorem ambientPostcompNaturality (G : Y ⟶ Z) :
    ∀ {F F' : X ⟶ Y} (eta : F ⟶ F'),
      ((ambientEquivalence X Y).inverse ⋙
          Bicategory.postcomp X.toFiberedCategoryOver (toMor G) ⋙
            (ambientEquivalence X Z).functor).map eta ≫ (Iso.refl (F' ≫ G)).hom =
        (Iso.refl (F ≫ G)).hom ≫ (Bicategory.postcomp X G).map eta := sorry

/-- Passing from bundled stack morphisms to ambient morphisms, postcomposing, and bundling again
agrees naturally with postcomposition in the stack bicategory. -/
@[stacks 04WS "ambient postcomposition comparison"]
noncomputable def ambientPostcompIso (G : Y ⟶ Z) :
    (ambientEquivalence X Y).inverse ⋙
        Bicategory.postcomp X.toFiberedCategoryOver (toMor G) ⋙
          (ambientEquivalence X Z).functor ≅
      Bicategory.postcomp X G :=
  NatIso.ofComponents (fun F ↦ Iso.refl (F ≫ G))
    (ambientPostcompNaturality G)

/-- The forward component of ambient postcomposition compatibility is the identity `2`-cell. -/
@[simp]
theorem ambientPostcompIso.hom.app (G : Y ⟶ Z) (F : X ⟶ Y) :
    (ambientPostcompIso G).hom.app F = 𝟙 (F ≫ G) := sorry

/-- The inverse component of ambient postcomposition compatibility is the identity `2`-cell. -/
@[simp]
theorem ambientPostcompIso.inv.app (G : Y ⟶ Z) (F : X ⟶ Y) :
    (ambientPostcompIso G).inv.app F = 𝟙 (F ≫ G) := sorry

end StackOver.Hom

end CategoryTheory
