/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.Composition.Interchange
public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Realization
public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy

/-!
@stack 0G5R

# Interchange homotopy for iterated endofunctor resolutions

Precomposition and postcomposition of augmentation-compatible maps commute up to a canonical
simplicial homotopy. The realization witness supplies the degree splitting needed to define its
components without choosing a particular resolution presentation.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.SimplicialObject
open Opposite
open scoped Simplicial

universe uA uB uC vA vB vC

namespace CategoryTheory

namespace EndofunctorResolution

namespace Realization

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
variable {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
variable {X : SimplicialObject (C ⥤ C)}

namespace interchange

/-- Split a pre/postcomposed realization degree into the two blocks selected by `i`, with the
associators needed for horizontal composition made explicit. -/
@[stacks 0G5R "factorization of a pre/postcomposed realization degree"]
def splitIso
    (hX : EndofunctorResolution.Realization d s X)
    (F : A ⥤ C) (G : C ⥤ B) (n : ℕ) (i : Fin (n + 1)) :
    F ⋙ (X _⦋n + 1⦌ ⋙ G) ≅
      (F ⋙ X _⦋n - i.1⦌) ⋙ (X _⦋i.1⦌ ⋙ G) :=
  Functor.isoWhiskerLeft F
      (Functor.isoWhiskerRight
        (EndofunctorResolution.Realization.splitIso hX n i) G) ≪≫
    Functor.isoWhiskerLeft F
      (Functor.associator (X _⦋n - i.1⦌) (X _⦋i.1⦌) G) ≪≫
    (Functor.associator F (X _⦋n - i.1⦌) (X _⦋i.1⦌ ⋙ G)).symm

/-- The degreewise map of the interchange homotopy.  After the `i`-th degeneracy it applies the
left component of `β` to the left block and the left component of `α` to the right block. -/
@[stacks 0G5R "component of the pre/postcomposition interchange homotopy"]
def component
    (hX : EndofunctorResolution.Realization d s X)
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α :
      SimplicialObject.Augmented.postcompose G hX.augmentation ⟶
        SimplicialObject.Augmented.postcompose G' hX.augmentation)
    (β :
      SimplicialObject.Augmented.precompose F hX.augmentation ⟶
        SimplicialObject.Augmented.precompose F' hX.augmentation)
    {n : ℕ} (i : Fin (n + 1)) :
    (SimplicialObject.Augmented.whisker F G hX.augmentation).left _⦋n⦌ ⟶
      (SimplicialObject.Augmented.whisker F' G' hX.augmentation).left
        _⦋n + 1⦌ :=
  Functor.whiskerLeft F (Functor.whiskerRight (X.σ i) G) ≫
    (splitIso hX F G n i).hom ≫
    (β.left.app (op ⦋n - i.1⦌) ◫ α.left.app (op ⦋i.1⦌)) ≫
    (splitIso hX F' G' n i).inv

/-- The zero face of the interchange component is the `α.right ⋆ β.left` endpoint. -/
@[stacks 0G5R "zero face of the pre/postcomposition interchange homotopy"]
theorem component.zero
    (hX : EndofunctorResolution.Realization d s X)
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : SimplicialObject.Augmented.postcompose G hX.augmentation ⟶
      SimplicialObject.Augmented.postcompose G' hX.augmentation)
    (β : SimplicialObject.Augmented.precompose F hX.augmentation ⟶
      SimplicialObject.Augmented.precompose F' hX.augmentation)
    (n : ℕ) :
    component hX α β (0 : Fin (n + 1)) ≫
        (SimplicialObject.Augmented.whisker F' G' hX.augmentation).left.δ 0 =
      (SimplicialObject.Augmented.whisker.interchange.rightLeft α β).left.app
        (op ⦋n⦌) := sorry

/-- The last face of the interchange component is the `α.left ⋆ β.right` endpoint. -/
@[stacks 0G5R "last face of the pre/postcomposition interchange homotopy"]
theorem component.last
    (hX : EndofunctorResolution.Realization d s X)
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : SimplicialObject.Augmented.postcompose G hX.augmentation ⟶
      SimplicialObject.Augmented.postcompose G' hX.augmentation)
    (β : SimplicialObject.Augmented.precompose F hX.augmentation ⟶
      SimplicialObject.Augmented.precompose F' hX.augmentation)
    (n : ℕ) :
    component hX α β (Fin.last n) ≫
        (SimplicialObject.Augmented.whisker F' G' hX.augmentation).left.δ
          (Fin.last (n + 1)) =
      (SimplicialObject.Augmented.whisker.interchange.leftRight α β).left.app
        (op ⦋n⦌) := sorry

/-- A face before the homotopy index commutes with the interchange component. -/
@[stacks 0G5R "face before a pre/postcomposition interchange index"]
theorem component.faceBefore
    (hX : EndofunctorResolution.Realization d s X)
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : SimplicialObject.Augmented.postcompose G hX.augmentation ⟶
      SimplicialObject.Augmented.postcompose G' hX.augmentation)
    (β : SimplicialObject.Augmented.precompose F hX.augmentation ⟶
      SimplicialObject.Augmented.precompose F' hX.augmentation)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    component hX α β j.succ ≫
        (SimplicialObject.Augmented.whisker F' G' hX.augmentation).left.δ i.castSucc =
      (SimplicialObject.Augmented.whisker F G hX.augmentation).left.δ i ≫
        component hX α β j := sorry

/-- The two adjacent face formulas for the interchange component agree. -/
@[stacks 0G5R "adjacent faces of the pre/postcomposition interchange homotopy"]
theorem component.faceAdjacent
    (hX : EndofunctorResolution.Realization d s X)
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : SimplicialObject.Augmented.postcompose G hX.augmentation ⟶
      SimplicialObject.Augmented.postcompose G' hX.augmentation)
    (β : SimplicialObject.Augmented.precompose F hX.augmentation ⟶
      SimplicialObject.Augmented.precompose F' hX.augmentation)
    {n : ℕ} (j : Fin (n + 1)) :
    component hX α β j.succ ≫
        (SimplicialObject.Augmented.whisker F' G' hX.augmentation).left.δ
          j.castSucc.succ =
      component hX α β j.castSucc ≫
        (SimplicialObject.Augmented.whisker F' G' hX.augmentation).left.δ
          j.castSucc.succ := sorry

/-- A face after the homotopy index commutes with the interchange component. -/
@[stacks 0G5R "face after a pre/postcomposition interchange index"]
theorem component.faceAfter
    (hX : EndofunctorResolution.Realization d s X)
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : SimplicialObject.Augmented.postcompose G hX.augmentation ⟶
      SimplicialObject.Augmented.postcompose G' hX.augmentation)
    (β : SimplicialObject.Augmented.precompose F hX.augmentation ⟶
      SimplicialObject.Augmented.precompose F' hX.augmentation)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    component hX α β j.castSucc ≫
        (SimplicialObject.Augmented.whisker F' G' hX.augmentation).left.δ i.succ =
      (SimplicialObject.Augmented.whisker F G hX.augmentation).left.δ i ≫
        component hX α β j := sorry

/-- A degeneracy before the homotopy index commutes with the interchange component. -/
@[stacks 0G5R "degeneracy before a pre/postcomposition interchange index"]
theorem component.degeneracyBefore
    (hX : EndofunctorResolution.Realization d s X)
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : SimplicialObject.Augmented.postcompose G hX.augmentation ⟶
      SimplicialObject.Augmented.postcompose G' hX.augmentation)
    (β : SimplicialObject.Augmented.precompose F hX.augmentation ⟶
      SimplicialObject.Augmented.precompose F' hX.augmentation)
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    component hX α β j ≫
        (SimplicialObject.Augmented.whisker F' G' hX.augmentation).left.σ i.castSucc =
      (SimplicialObject.Augmented.whisker F G hX.augmentation).left.σ i ≫
        component hX α β j.succ := sorry

/-- A degeneracy after the homotopy index commutes with the interchange component. -/
@[stacks 0G5R "degeneracy after a pre/postcomposition interchange index"]
theorem component.degeneracyAfter
    (hX : EndofunctorResolution.Realization d s X)
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : SimplicialObject.Augmented.postcompose G hX.augmentation ⟶
      SimplicialObject.Augmented.postcompose G' hX.augmentation)
    (β : SimplicialObject.Augmented.precompose F hX.augmentation ⟶
      SimplicialObject.Augmented.precompose F' hX.augmentation)
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    component hX α β j ≫
        (SimplicialObject.Augmented.whisker F' G' hX.augmentation).left.σ i.succ =
      (SimplicialObject.Augmented.whisker F G hX.augmentation).left.σ i ≫
        component hX α β j.castSucc := sorry

/-- The concrete directed homotopy between the two horizontal composites attached to a pair of
augmentation-compatible simplicial maps. -/
@[stacks 0G5R "pre/postcomposition interchange simplicial homotopy"]
def homotopy
    (hX : EndofunctorResolution.Realization d s X)
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : SimplicialObject.Augmented.postcompose G hX.augmentation ⟶
      SimplicialObject.Augmented.postcompose G' hX.augmentation)
    (β : SimplicialObject.Augmented.precompose F hX.augmentation ⟶
      SimplicialObject.Augmented.precompose F' hX.augmentation) :
    Homotopy
      (SimplicialObject.Augmented.whisker.interchange.leftRight α β).left
      (SimplicialObject.Augmented.whisker.interchange.rightLeft α β).left where
  h := component hX α β
  h_zero_comp_δ_zero := component.zero hX α β
  h_last_comp_δ_last := component.last hX α β
  h_succ_comp_δ_castSucc_of_lt := component.faceBefore hX α β
  h_succ_comp_δ_castSucc_succ := component.faceAdjacent hX α β
  h_castSucc_comp_δ_succ_of_lt := component.faceAfter hX α β
  h_comp_σ_castSucc_of_le := component.degeneracyBefore hX α β
  h_comp_σ_succ_of_lt := component.degeneracyAfter hX α β

/-- The interchange homotopy gives the symmetric reusable homotopy relation between the two
horizontal composites. -/
@[stacks 0G5R "pre/postcomposition interchange homotopy relation"]
theorem homotopic
    (hX : EndofunctorResolution.Realization d s X)
    {F F' : A ⥤ C} {G G' : C ⥤ B}
    (α : SimplicialObject.Augmented.postcompose G hX.augmentation ⟶
      SimplicialObject.Augmented.postcompose G' hX.augmentation)
    (β : SimplicialObject.Augmented.precompose F hX.augmentation ⟶
      SimplicialObject.Augmented.precompose F' hX.augmentation) :
    Homotopic
      (SimplicialObject.Augmented.whisker.interchange.leftRight α β).left
      (SimplicialObject.Augmented.whisker.interchange.rightLeft α β).left := sorry

end interchange

end Realization

end EndofunctorResolution

end CategoryTheory
