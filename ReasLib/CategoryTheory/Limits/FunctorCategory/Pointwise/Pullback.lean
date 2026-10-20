/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.FunctorCategory.Pointwise.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 016T

# Pointwise pullbacks in functor categories

This file supplies pullbacks from objectwise hypotheses and records evaluation comparison maps and
isomorphisms without requiring all pullbacks in the target category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v v' u u'

namespace CategoryTheory.Limits.FunctorCategory

variable {K : Type u} [Category.{v} K]
variable {C : Type u'} [Category.{v'} C]

section Pullback

variable {X Y Z : K ⥤ C} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- `HasPointwisePullback f g` records only the pullbacks of the component cospans of `f` and
`g`, rather than requiring every pullback in `C`. -/
@[stacks 016T "pointwise existence of a pullback of functors"]
class HasPointwisePullback : Prop where
  /-- Every evaluated cospan has its required pullback. -/
  hasPullback (k : K) : HasPullback (f.app k) (g.app k)

attribute [instance] HasPointwisePullback.hasPullback

namespace HasPointwisePullback

/-- Pullbacks in the target category supply pointwise pullbacks for every cospan of functors. -/
@[stacks 016T "pointwise pullbacks from pullbacks"]
instance ofPullbacks [HasPullbacks C] : HasPointwisePullback f g where
  hasPullback _ := inferInstance

end HasPointwisePullback

/-- A pointwise pullback supplies the pullback in the exact form requested by an evaluation
functor. -/
@[stacks 016T "evaluated cospan pullback"]
instance (priority := low) pointwise.cospan.hasPullback
    [HasPointwisePullback f g] (k : K) :
    HasPullback (((evaluation K C).obj k).map f)
      (((evaluation K C).obj k).map g) :=
  (inferInstance : HasPointwisePullback f g).hasPullback k

/-- The evaluated cospan diagram has a limit whenever the corresponding component maps have a
pullback. -/
@[stacks 016T "objectwise cospan limit"]
noncomputable instance (priority := low) pointwise.cospan.hasLimit
    [HasPointwisePullback f g] (k : K) :
    HasLimit ((cospan f g).flip.obj k) :=
  hasLimit_of_iso (cospanCompIso ((evaluation K C).obj k) f g).symm

/-- Objectwise pullbacks give the pullback in the functor category. -/
@[stacks 016T "pointwise pullback of functors"]
public noncomputable abbrev pointwise.pullback
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPointwisePullback f g] :
    HasPullback f g :=
  functorCategoryHasLimit (cospan f g)

/-- Evaluation identifies a functor-category pullback with the corresponding objectwise pullback.
This generic comparison is shared by the pointwise-pullback and pullback-comparison facades. -/
@[stacks 016T "pointwise pullback comparison", stacks 0172]
noncomputable def evaluation.pullbackIso
    [HasPointwisePullback f g] (k : K) :
    (pullback f g).obj k ≅ pullback (f.app k) (g.app k) :=
  evaluation.limitIso (cospan f g) k ≪≫
    HasLimit.isoOfNatIso (cospanCompIso ((evaluation K C).obj k) f g)

/-- The canonical map between two evaluated pullbacks induced by a morphism of the indexing
category.  The naturality squares of `f` and `g` supply the compatibility proofs internally. -/
@[stacks 016T "pointwise pullback structure map", stacks 0172]
noncomputable def evaluation.pullbackMap [HasPointwisePullback f g]
    {k l : K} (h : k ⟶ l) :
    pullback (f.app k) (g.app k) ⟶ pullback (f.app l) (g.app l) :=
  pullback.map (f.app k) (g.app k) (f.app l) (g.app l)
    (X.map h) (Y.map h) (Z.map h) (f.naturality h).symm (g.naturality h).symm

/-- The first projection of `evaluation.pullbackMap` is the first structure map. -/
@[reassoc (attr := simp), stacks 016T "first projection of the pointwise pullback map", stacks 0172]
theorem evaluation.pullbackMap.fst [HasPointwisePullback f g]
    {k l : K} (h : k ⟶ l) :
    evaluation.pullbackMap f g h ≫ pullback.fst (f.app l) (g.app l) =
      pullback.fst (f.app k) (g.app k) ≫ X.map h := sorry

/-- The second projection of `evaluation.pullbackMap` is the second structure map. -/
@[reassoc (attr := simp), stacks 016T "second projection of the pointwise pullback map", stacks 0172]
theorem evaluation.pullbackMap.snd [HasPointwisePullback f g]
    {k l : K} (h : k ⟶ l) :
    evaluation.pullbackMap f g h ≫ pullback.snd (f.app l) (g.app l) =
      pullback.snd (f.app k) (g.app k) ≫ Y.map h := sorry

/-- The first projection of `evaluation.pullbackIso` is the evaluated first projection. -/
@[reassoc (attr := simp), stacks 016T "pointwise pullback first projection", stacks 0172]
theorem evaluation.pullbackIso.fst
    [HasPointwisePullback f g] (k : K) :
    (evaluation.pullbackIso f g k).hom ≫ pullback.fst (f.app k) (g.app k) =
      (pullback.fst f g).app k := sorry

/-- The second projection of `evaluation.pullbackIso` is the evaluated second projection. -/
@[reassoc (attr := simp), stacks 016T "pointwise pullback second projection", stacks 0172]
theorem evaluation.pullbackIso.snd
    [HasPointwisePullback f g] (k : K) :
    (evaluation.pullbackIso f g k).hom ≫ pullback.snd (f.app k) (g.app k) =
      (pullback.snd f g).app k := sorry

/-- The inverse comparison carries the evaluated first projection back to the pointwise first
projection. -/
@[reassoc (attr := simp), stacks 016T "inverse pointwise pullback first projection", stacks 0172]
theorem evaluation.pullbackIso.inv_fst
    [HasPointwisePullback f g] (k : K) :
    (evaluation.pullbackIso f g k).inv ≫ (pullback.fst f g).app k =
      pullback.fst (f.app k) (g.app k) := sorry

/-- The inverse comparison carries the evaluated second projection back to the pointwise second
projection. -/
@[reassoc (attr := simp), stacks 016T "inverse pointwise pullback second projection", stacks 0172]
theorem evaluation.pullbackIso.inv_snd
    [HasPointwisePullback f g] (k : K) :
    (evaluation.pullbackIso f g k).inv ≫ (pullback.snd f g).app k =
      pullback.snd (f.app k) (g.app k) := sorry

/-- Under the evaluation comparisons, the structure map of a pullback of functors is the
canonical map between the corresponding pointwise pullbacks. -/
@[reassoc, stacks 016T "comparison for a pointwise pullback structure map", stacks 0172]
theorem evaluation.pullbackIso.map [HasPointwisePullback f g]
    {k l : K} (h : k ⟶ l) :
    (pullback f g).map h ≫ (evaluation.pullbackIso f g l).hom =
      (evaluation.pullbackIso f g k).hom ≫ evaluation.pullbackMap f g h := sorry

/-- The inverse pullback comparisons are natural in the evaluation object. -/
@[reassoc, stacks 016T "inverse pointwise pullback structure map", stacks 0172]
theorem evaluation.pullbackIso.inv_map [HasPointwisePullback f g]
    {k l : K} (h : k ⟶ l) :
    (evaluation.pullbackIso f g k).inv ≫ (pullback f g).map h =
      evaluation.pullbackMap f g h ≫ (evaluation.pullbackIso f g l).inv := sorry

end Pullback

end CategoryTheory.Limits.FunctorCategory
