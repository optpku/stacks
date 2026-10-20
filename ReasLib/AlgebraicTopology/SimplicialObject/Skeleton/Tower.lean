/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.CategoryTheory.Functor.OfSequence.Colimit

/-!
# The skeleton tower of a simplicial object

The skeleton adjunctions give canonical transition maps from the `n`-skeleton to the
`(n + 1)`-skeleton.  These maps form a sequential diagram equipped with the canonical cocone to
the original simplicial object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Skeleton

variable {A : Type u} [Category.{v} A]

/-- The canonical transition from the `n`-skeleton of `V` to its `(n + 1)`-skeleton. -/
@[stacks 0193 "skeleton tower transition"]
noncomputable def succMap (V : SimplicialObject A) (n : ℕ)
    [Truncated.HasSkeletons A n] [Truncated.HasSkeletons A (n + 1)] :
    (sk n).obj V ⟶ (sk (n + 1)).obj V :=
  ((skAdj n).homEquiv ((truncation n).obj V) ((sk (n + 1)).obj V)).symm
    (((truncationCompTrunc (Nat.le_succ n)).app V).inv ≫
      (Truncated.trunc A (n + 1) n).map
        ((skAdj (n + 1)).unit.app ((truncation (n + 1)).obj V)) ≫
      ((truncationCompTrunc (Nat.le_succ n)).app ((sk (n + 1)).obj V)).hom)

/-- The skeleton transitions are compatible with the counits to the original simplicial
object. -/
@[reassoc, stacks 0193 "skeleton transition and counit"]
theorem succMap_comp_counit (V : SimplicialObject A) (n : ℕ)
    [Truncated.HasSkeletons A n] [Truncated.HasSkeletons A (n + 1)] :
    succMap V n ≫ (skAdj (n + 1)).counit.app V = (skAdj n).counit.app V := sorry

namespace Tower

/-- The skeleton transition is natural in the simplicial object. -/
@[stacks 0193 "naturality of a skeleton tower transition"]
theorem step_naturality (n : ℕ)
    [Truncated.HasSkeletons A n] [Truncated.HasSkeletons A (n + 1)]
    {V W : SimplicialObject A} (f : V ⟶ W) :
    (sk (C := A) n).map f ≫ succMap W n =
      succMap V n ≫ (sk (C := A) (n + 1)).map f := sorry

/-- The canonical natural transition from the `n`-skeleton endofunctor to the
`(n + 1)`-skeleton endofunctor. -/
@[stacks 0193 "natural skeleton tower transition"]
noncomputable def step (n : ℕ)
    [Truncated.HasSkeletons A n] [Truncated.HasSkeletons A (n + 1)] :
    sk (C := A) n ⟶ sk (C := A) (n + 1) where
  app V := succMap V n
  naturality _ _ f := step_naturality n f

/-- Evaluating the natural skeleton transition gives the objectwise transition. -/
@[simp, stacks 0193 "objectwise skeleton tower transition"]
theorem step_app (V : SimplicialObject A) (n : ℕ)
    [Truncated.HasSkeletons A n] [Truncated.HasSkeletons A (n + 1)] :
    (step n).app V = succMap V n := sorry

/-- The skeleton transitions commute with the adjunction counits as natural
transformations. -/
@[stacks 0193 "skeleton tower transition and counit"]
theorem step_comp_counit (n : ℕ)
    [Truncated.HasSkeletons A n] [Truncated.HasSkeletons A (n + 1)] :
    step (A := A) n ≫ (skAdj (C := A) (n + 1)).counit =
      (skAdj (C := A) n).counit := sorry

variable [∀ n, Truncated.HasSkeletons A n]

/-- The skeleton tower as a sequential diagram in the category of endofunctors of
simplicial objects. -/
@[stacks 0193 "functorial skeleton tower"]
noncomputable def diagram : ℕ ⥤ (SimplicialObject A ⥤ SimplicialObject A) :=
  Functor.ofSequence (fun n ↦ step (A := A) n)

/-- The endofunctor at stage `n` of the skeleton tower is `sk n`. -/
@[simp, stacks 0193 "skeleton tower stage"]
theorem diagram_obj (n : ℕ) :
    (diagram (A := A)).obj n = sk (C := A) n := sorry

/-- The successor map of the functorial skeleton tower is its canonical transition. -/
@[simp, stacks 0193 "skeleton tower successor map"]
theorem diagram_map_succ (n : ℕ) :
    (diagram (A := A)).map (homOfLE (Nat.le_succ n)) = step (A := A) n := sorry

namespace diagram

/-- Every map in the functorial skeleton tower factors the source-stage counit through the
target-stage counit. -/
@[reassoc, stacks 0193 "compatibility of a functorial skeleton tower map with the counit"]
theorem map_comp_counit {i j : ℕ} (f : i ⟶ j) :
    (Tower.diagram (A := A)).map f ≫ (skAdj (C := A) j).counit =
      (skAdj (C := A) i).counit := sorry

end diagram

/-- The canonical cocone from the functorial skeleton tower to the identity
endofunctor. -/
@[stacks 0193 "functorial cocone from the skeleton tower"]
noncomputable def cocone : Cocone (diagram (A := A)) :=
  Functor.ofSequence.constCocone (fun n ↦ step (A := A) n)
    (fun n ↦ (skAdj (C := A) n).counit)
    (fun n ↦ step_comp_counit (A := A) n)

/-- The point of the functorial skeleton cocone is the identity endofunctor. -/
@[simp, stacks 0193 "skeleton tower cocone point"]
theorem cocone_pt :
    (cocone (A := A)).pt = 𝟭 (SimplicialObject A) := sorry

/-- A leg of the functorial skeleton cocone is the corresponding adjunction counit. -/
@[simp, stacks 0193 "skeleton tower cocone leg"]
theorem cocone_ι_app (n : ℕ) :
    (cocone (A := A)).ι.app n = (skAdj (C := A) n).counit := sorry

end Tower

variable [∀ n, Truncated.HasSkeletons A n]

/-- The sequential diagram formed by the skeleta of `V`. -/
@[stacks 0193 "skeleton tower"]
noncomputable def sequence (V : SimplicialObject A) : ℕ ⥤ SimplicialObject A :=
  Tower.diagram (A := A) ⋙
    (evaluation (SimplicialObject A) (SimplicialObject A)).obj V

/-- The object at stage `n` of the skeleton sequence is the `n`-skeleton. -/
@[simp, stacks 0193 "skeleton sequence stage"]
theorem sequence_obj (V : SimplicialObject A) (n : ℕ) :
    (sequence V).obj n = (sk n).obj V := sorry

/-- The successor component of the skeleton sequence is its canonical transition map. -/
@[simp, stacks 0193 "skeleton sequence successor map"]
theorem sequence_map_succ (V : SimplicialObject A) (n : ℕ) :
    (sequence V).map (homOfLE (Nat.le_succ n)) = succMap V n := sorry

namespace sequence

/-- Every map in a skeleton sequence factors the source-stage counit through the target-stage
counit. -/
@[stacks 0193 "compatibility of a skeleton sequence map with the counit", reassoc]
theorem map_comp_counit (V : SimplicialObject A) {i j : ℕ} (f : i ⟶ j) :
    (sequence V).map f ≫ (skAdj j).counit.app V = (skAdj i).counit.app V := sorry

end sequence

/-- The canonical cocone from the skeleton sequence of `V` to `V`. -/
@[stacks 0193 "cocone from the skeleton tower"]
noncomputable def cocone (V : SimplicialObject A) : Cocone (sequence V) :=
  ((evaluation (SimplicialObject A) (SimplicialObject A)).obj V).mapCocone
    (Tower.cocone (A := A))

/-- A leg of the skeleton cocone is the counit of the corresponding skeleton adjunction. -/
@[simp, stacks 0193 "skeleton sequence cocone leg"]
theorem cocone_ι_app (V : SimplicialObject A) (n : ℕ) :
    (cocone V).ι.app n = (skAdj n).counit.app V := sorry

end CategoryTheory.SimplicialObject.Skeleton
