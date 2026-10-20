module

public import ReasLib.CategoryTheory.Limits.FunctorCategory.Pointwise.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 016W

# Pointwise pushouts in functor categories

This file supplies pushouts from objectwise hypotheses and records evaluation comparison maps and
isomorphisms without requiring all pushouts in the target category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v v' u u'

namespace CategoryTheory.Limits.FunctorCategory

variable {K : Type u} [Category.{v} K]
variable {C : Type u'} [Category.{v'} C]

section Pushout

variable {X Y Z : K ⥤ C} (f : Z ⟶ X) (g : Z ⟶ Y)

/-- `HasPointwisePushout f g` records only the pushouts of the component spans of `f` and `g`,
rather than requiring every pushout in `C`. -/
@[stacks 016W "pointwise existence of a pushout of functors"]
class HasPointwisePushout : Prop where
  /-- Every evaluated span has its required pushout. -/
  hasPushout (k : K) : HasPushout (f.app k) (g.app k)

attribute [instance] HasPointwisePushout.hasPushout

namespace HasPointwisePushout

/-- Pushouts in the target category supply pointwise pushouts for every span of functors. -/
@[stacks 016W "pointwise pushouts from pushouts"]
instance ofPushouts [HasPushouts C] : HasPointwisePushout f g where
  hasPushout _ := inferInstance

end HasPointwisePushout

/-- A pointwise pushout supplies the pushout in the exact form requested by an evaluation
functor. -/
@[stacks 016W "evaluated span pushout"]
instance (priority := low) pointwise.span.hasPushout
    [HasPointwisePushout f g] (k : K) :
    HasPushout (((evaluation K C).obj k).map f)
      (((evaluation K C).obj k).map g) :=
  (inferInstance : HasPointwisePushout f g).hasPushout k

/-- The evaluated span diagram has a colimit whenever the corresponding component maps have a
pushout. -/
@[stacks 016W "objectwise span colimit"]
noncomputable instance (priority := low) pointwise.span.hasColimit
    [HasPointwisePushout f g] (k : K) :
    HasColimit ((span f g).flip.obj k) :=
  hasColimit_of_iso (spanCompIso ((evaluation K C).obj k) f g)

/-- Objectwise pushouts give the pushout in the functor category. -/
@[stacks 016W "pointwise pushout of functors"]
public noncomputable abbrev pointwise.pushout
    (f : Z ⟶ X) (g : Z ⟶ Y) [HasPointwisePushout f g] :
    HasPushout f g :=
  functorCategoryHasColimit (span f g)

/-- Evaluation identifies a functor-category pushout with the corresponding objectwise
pushout. -/
@[stacks 016W]
noncomputable def evaluation.pushoutIso
    [HasPointwisePushout f g] (k : K) :
    (pushout f g).obj k ≅ pushout (f.app k) (g.app k) :=
  evaluation.colimitIso (span f g) k ≪≫
    HasColimit.isoOfNatIso (spanCompIso ((evaluation K C).obj k) f g)

/-- The canonical map between two evaluated pushouts induced by a morphism of the indexing
category.  The naturality squares of `f` and `g` supply the compatibility proofs internally. -/
@[stacks 016W "pointwise pushout structure map"]
noncomputable def evaluation.pushoutMap [HasPointwisePushout f g]
    {k l : K} (h : k ⟶ l) :
    pushout (f.app k) (g.app k) ⟶ pushout (f.app l) (g.app l) :=
  pushout.map (f.app k) (g.app k) (f.app l) (g.app l)
    (X.map h) (Y.map h) (Z.map h) (f.naturality h).symm (g.naturality h).symm

/-- The first inclusion commutes with `evaluation.pushoutMap`. -/
@[reassoc (attr := simp), stacks 016W "first inclusion of the pointwise pushout map"]
theorem evaluation.pushoutMap.inl [HasPointwisePushout f g]
    {k l : K} (h : k ⟶ l) :
    pushout.inl (f.app k) (g.app k) ≫ evaluation.pushoutMap f g h =
      X.map h ≫ pushout.inl (f.app l) (g.app l) := sorry

/-- The second inclusion commutes with `evaluation.pushoutMap`. -/
@[reassoc (attr := simp), stacks 016W "second inclusion of the pointwise pushout map"]
theorem evaluation.pushoutMap.inr [HasPointwisePushout f g]
    {k l : K} (h : k ⟶ l) :
    pushout.inr (f.app k) (g.app k) ≫ evaluation.pushoutMap f g h =
      Y.map h ≫ pushout.inr (f.app l) (g.app l) := sorry

/-- The first inclusion into `evaluation.pushoutIso` is the evaluated first inclusion. -/
@[reassoc (attr := simp), stacks 016W]
theorem evaluation.pushoutIso.inl
    [HasPointwisePushout f g] (k : K) :
    (pushout.inl f g).app k ≫ (evaluation.pushoutIso f g k).hom =
      pushout.inl (f.app k) (g.app k) := sorry

/-- The second inclusion into `evaluation.pushoutIso` is the evaluated second inclusion. -/
@[reassoc (attr := simp), stacks 016W]
theorem evaluation.pushoutIso.inr
    [HasPointwisePushout f g] (k : K) :
    (pushout.inr f g).app k ≫ (evaluation.pushoutIso f g k).hom =
      pushout.inr (f.app k) (g.app k) := sorry

/-- The inverse comparison carries the evaluated first inclusion back to the pointwise first
inclusion. -/
@[reassoc (attr := simp), stacks 016W "inverse pointwise pushout first inclusion"]
theorem evaluation.pushoutIso.inl_inv
    [HasPointwisePushout f g] (k : K) :
    pushout.inl (f.app k) (g.app k) ≫ (evaluation.pushoutIso f g k).inv =
      (pushout.inl f g).app k := sorry

/-- The inverse comparison carries the evaluated second inclusion back to the pointwise second
inclusion. -/
@[reassoc (attr := simp), stacks 016W "inverse pointwise pushout second inclusion"]
theorem evaluation.pushoutIso.inr_inv
    [HasPointwisePushout f g] (k : K) :
    pushout.inr (f.app k) (g.app k) ≫ (evaluation.pushoutIso f g k).inv =
      (pushout.inr f g).app k := sorry

/-- Under the evaluation comparisons, the structure map of a pushout of functors is the
canonical map between the corresponding pointwise pushouts. -/
@[reassoc, stacks 016W "comparison for a pointwise pushout structure map"]
theorem evaluation.pushoutIso.map [HasPointwisePushout f g]
    {k l : K} (h : k ⟶ l) :
    (pushout f g).map h ≫ (evaluation.pushoutIso f g l).hom =
      (evaluation.pushoutIso f g k).hom ≫ evaluation.pushoutMap f g h := sorry

/-- The inverse pushout comparisons are natural in the evaluation object. -/
@[reassoc, stacks 016W "inverse pointwise pushout structure map"]
theorem evaluation.pushoutIso.inv_map [HasPointwisePushout f g]
    {k l : K} (h : k ⟶ l) :
    (evaluation.pushoutIso f g k).inv ≫ (pushout f g).map h =
      evaluation.pushoutMap f g h ≫ (evaluation.pushoutIso f g l).inv := sorry

end Pushout

end CategoryTheory.Limits.FunctorCategory
