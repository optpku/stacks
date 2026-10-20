/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmented.Center
public import ReasLib.CategoryTheory.Endofunctor.ComonadResolution.Realization
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Center
public import ReasLib.CategoryTheory.Endofunctor.Iteration.Simplicial
public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy

/-!
@stack 0G5S

# Identity-whiskering homotopy for iterated endofunctor resolutions

A central endomorphism acts on the two sides of an endofunctor-valued simplicial object.  Any
realization of iterated-endofunctor data carries a canonical simplicial homotopy between these
two actions.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.SimplicialObject
open Opposite
open scoped Simplicial

universe uC vC

namespace CategoryTheory

namespace EndofunctorResolution

namespace Realization

variable {C : Type uC} [Category.{vC} C]
variable {Y : C ⥤ C} {d : Y ⟶ 𝟭 C} {s : Y ⟶ Y ⋙ Y}
variable {X : SimplicialObject (C ⥤ C)}

namespace whisker

/-- The degreewise component of the canonical homotopy from left to right identity-whiskering.
It duplicates the factor selected by `i` and inserts the central endomorphism between the two
resulting positive-iterate blocks.  The common index in `degeneracy` and `centerAt` incorporates
the reversal between the endpoint convention of the Stacks cylinder family and Mathlib's
directed `Homotopy`. -/
@[stacks 0G5S "component of the identity-whiskering homotopy"]
def component
    (hX : EndofunctorResolution.Realization d s X) (z : CatCenter C)
    {n : ℕ} (i : Fin (n + 1)) :
    X.obj (op ⦋n⦌) ⟶ X.obj (op ⦋n + 1⦌) :=
  (hX.objIso n).hom ≫
    IteratedEndofunctor.degeneracy s n i ≫
    IteratedEndofunctor.centerAt Y z n i ≫
    (hX.objIso (n + 1)).inv

/-- The initial face of the identity-whiskering homotopy component is right whiskering. -/
@[stacks 0G5S "initial face of the identity-whiskering homotopy"]
theorem component.zero
    (hX : EndofunctorResolution.Realization d s X) (z : CatCenter C) (n : ℕ) :
    component hX z (0 : Fin (n + 1)) ≫ X.δ (0 : Fin (n + 2)) =
      (Functor.whiskerLeft X (CatCenter.whiskerLeft C z)).app (op ⦋n⦌) := sorry

/-- The final face of the identity-whiskering homotopy component is left whiskering. -/
@[stacks 0G5S "final face of the identity-whiskering homotopy"]
theorem component.last
    (hX : EndofunctorResolution.Realization d s X) (z : CatCenter C) (n : ℕ) :
    component hX z (Fin.last n) ≫ X.δ (Fin.last (n + 1)) =
      (Functor.whiskerLeft X (CatCenter.whiskerRight C z)).app (op ⦋n⦌) := sorry

/-- A face before the homotopy index commutes with the identity-whiskering component. -/
@[stacks 0G5S "face before an identity-whiskering homotopy index"]
theorem component.faceBefore
    (hX : EndofunctorResolution.Realization d s X) (z : CatCenter C)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    component hX z j.succ ≫ X.δ i.castSucc =
      X.δ i ≫ component hX z j := sorry

/-- The two adjacent face formulas for the identity-whiskering component agree. -/
@[stacks 0G5S "adjacent faces of the identity-whiskering homotopy"]
theorem component.faceAdjacent
    (hX : EndofunctorResolution.Realization d s X) (z : CatCenter C)
    {n : ℕ} (j : Fin (n + 1)) :
    component hX z j.succ ≫ X.δ j.castSucc.succ =
      component hX z j.castSucc ≫ X.δ j.castSucc.succ := sorry

/-- A face after the homotopy index commutes with the identity-whiskering component. -/
@[stacks 0G5S "face after an identity-whiskering homotopy index"]
theorem component.faceAfter
    (hX : EndofunctorResolution.Realization d s X) (z : CatCenter C)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    component hX z j.castSucc ≫ X.δ i.succ =
      X.δ i ≫ component hX z j := sorry

/-- A degeneracy before the homotopy index commutes with the identity-whiskering component. -/
@[stacks 0G5S "degeneracy before an identity-whiskering homotopy index"]
theorem component.degeneracyBefore
    (hX : EndofunctorResolution.Realization d s X) (z : CatCenter C)
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    component hX z j ≫ X.σ i.castSucc =
      X.σ i ≫ component hX z j.succ := sorry

/-- A degeneracy after the homotopy index commutes with the identity-whiskering component. -/
@[stacks 0G5S "degeneracy after an identity-whiskering homotopy index"]
theorem component.degeneracyAfter
    (hX : EndofunctorResolution.Realization d s X) (z : CatCenter C)
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    component hX z j ≫ X.σ i.succ =
      X.σ i ≫ component hX z j.castSucc := sorry

/-- The canonical concrete simplicial homotopy from left to right whiskering by a central
endomorphism on any realization of iterated-endofunctor data. -/
@[stacks 0G5S "identity-whiskering simplicial homotopy"]
def homotopy
    (hX : EndofunctorResolution.Realization d s X) (z : CatCenter C) :
    Homotopy
      (Functor.whiskerLeft X (CatCenter.whiskerRight C z))
      (Functor.whiskerLeft X (CatCenter.whiskerLeft C z)) where
  h := component hX z
  h_zero_comp_δ_zero := component.zero hX z
  h_last_comp_δ_last := component.last hX z
  h_succ_comp_δ_castSucc_of_lt := component.faceBefore hX z
  h_succ_comp_δ_castSucc_succ := component.faceAdjacent hX z
  h_castSucc_comp_δ_succ_of_lt := component.faceAfter hX z
  h_comp_σ_castSucc_of_le := component.degeneracyBefore hX z
  h_comp_σ_succ_of_lt := component.degeneracyAfter hX z

/-- The directed identity-whiskering homotopy gives the symmetric reusable homotopy relation. -/
@[stacks 0G5S "identity-whiskering homotopy relation"]
theorem homotopic
    (hX : EndofunctorResolution.Realization d s X) (z : CatCenter C) :
    Homotopic
      (Functor.whiskerLeft X (CatCenter.whiskerRight C z))
      (Functor.whiskerLeft X (CatCenter.whiskerLeft C z)) := sorry

end whisker

end Realization

end EndofunctorResolution

end CategoryTheory
