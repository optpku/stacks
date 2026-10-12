/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Functor.Target
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Variance
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Pushout.IsPullback
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Pushout.Pullback.Map
public import ReasLib.CategoryTheory.Limits.FunctorCategory.Pointwise.Pullback

/-!
# The target functor of internal-hom pullbacks

The pullback square supplied by `IsPushout.internalHom` gives the canonical pointwise pullback
instances. The generic functor-category construction then assembles the pullback functor and its
evaluation comparisons without any additional objectwise pullback hypothesis.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject.internalHom.pushout.pullback

variable {C : Type uC} [Category.{vC} C]
variable {U V W : SSet.{uS}} (a : U ⟶ V) (b : U ⟶ W)
variable [HasCopowers U C] [HasCopowers V C] [HasCopowers W C]
variable [HasCopowers (CategoryTheory.Limits.pushout a b) C]
variable [HasInternalHoms U C] [HasInternalHoms V C] [HasInternalHoms W C]
variable [HasInternalHoms (CategoryTheory.Limits.pushout a b) C]

/-- The internal-hom pullback square supplies the exact pointwise pullbacks of the two
precomposition natural transformations. -/
@[stacks 017N "pointwise internal-hom pullback of a simplicial-set pushout span"]
instance hasPointwisePullback :
    Limits.FunctorCategory.HasPointwisePullback
      (precomp.natTrans (C := C) a) (precomp.natTrans (C := C) b) where
  hasPullback X :=
    (CategoryTheory.IsPushout.internalHom
      (show IsPushout a b (pushout.inl a b) (pushout.inr a b) from
        CategoryTheory.IsPushout.of_isColimit (pushout.isColimit a b)) X).hasPullback

/-- The pointwise projection cannot be inferred backwards from an `.app` target, so expose the
object-level pullback instance at this specialized owner. -/
@[stacks 017N "objectwise internal-hom pullback instance"]
instance hasPullback.obj (X : SimplicialObject C) :
    HasPullback (precomp a X) (precomp b X) :=
  (hasPointwisePullback (C := C) a b).hasPullback X

/-- The generic pointwise construction gives the canonical functor-category pullback of the two
precomposition natural transformations. -/
@[stacks 017N "functor-category internal-hom pullback of a span"]
noncomputable instance (priority := low) hasPullback :
    HasPullback (precomp.natTrans (C := C) a) (precomp.natTrans (C := C) b) :=
  Limits.FunctorCategory.pointwise.pullback
    (precomp.natTrans (C := C) a) (precomp.natTrans (C := C) b)

/-- For a fixed span of simplicial sets, the target is the canonical pullback of the
two precomposition natural transformations in the functor category. -/
@[stacks 017N "target functor on the internal-hom pullback of a span"]
noncomputable abbrev functor : SimplicialObject C ⥤ SimplicialObject C :=
  CategoryTheory.Limits.pullback
    (precomp.natTrans (C := C) a) (precomp.natTrans (C := C) b)

/-- The first projection from the canonical internal-hom pullback functor. -/
@[stacks 017N "first projection of the internal-hom pullback functor"]
noncomputable abbrev functor.fst :
    functor (C := C) a b ⟶ internalHom.targetFunctor (C := C) V :=
  CategoryTheory.Limits.pullback.fst
    (precomp.natTrans (C := C) a) (precomp.natTrans (C := C) b)

/-- The second projection from the canonical internal-hom pullback functor. -/
@[stacks 017N "second projection of the internal-hom pullback functor"]
noncomputable abbrev functor.snd :
    functor (C := C) a b ⟶ internalHom.targetFunctor (C := C) W :=
  CategoryTheory.Limits.pullback.snd
    (precomp.natTrans (C := C) a) (precomp.natTrans (C := C) b)

/-- The canonical pullback cone of the two internal-hom precomposition natural
transformations. -/
@[stacks 017N "pullback cone of the internal-hom restriction maps"]
noncomputable def functor.cone : PullbackCone
    (precomp.natTrans (C := C) a) (precomp.natTrans (C := C) b) :=
  PullbackCone.mk (functor.fst (C := C) a b) (functor.snd (C := C) a b)
    CategoryTheory.Limits.pullback.condition

/-- The canonical internal-hom pullback cone is limiting in the functor category. -/
@[stacks 017N "universal property of the internal-hom pullback functor"]
noncomputable def functor.isLimit : IsLimit (functor.cone (C := C) a b) :=
  CategoryTheory.Limits.pullbackIsPullback
    (precomp.natTrans (C := C) a) (precomp.natTrans (C := C) b)

/-- Evaluation identifies the canonical functor-category pullback with the chosen
objectwise pullback. -/
@[stacks 017N "evaluation of the internal-hom pullback functor"]
noncomputable def functor.objIso (X : SimplicialObject C) :
    (functor (C := C) a b).obj X ≅
      CategoryTheory.Limits.pullback (precomp a X) (precomp b X) :=
  Limits.FunctorCategory.evaluation.pullbackIso
    (precomp.natTrans (C := C) a) (precomp.natTrans (C := C) b) X

/-- The evaluated first projection agrees with the first objectwise pullback
projection under `functor.objIso`. -/
@[reassoc (attr := simp), stacks 017N "first projection of the evaluated pullback functor"]
theorem functor.objIso.fst (X : SimplicialObject C) :
    (functor.objIso (C := C) a b X).hom ≫
        CategoryTheory.Limits.pullback.fst (precomp a X) (precomp b X) =
      (functor.fst (C := C) a b).app X := sorry

/-- The evaluated second projection agrees with the second objectwise pullback
projection under `functor.objIso`. -/
@[reassoc (attr := simp), stacks 017N "second projection of the evaluated pullback functor"]
theorem functor.objIso.snd (X : SimplicialObject C) :
    (functor.objIso (C := C) a b X).hom ≫
        CategoryTheory.Limits.pullback.snd (precomp a X) (precomp b X) =
      (functor.snd (C := C) a b).app X := sorry

/-- The inverse evaluated first projection agrees with the objectwise pullback projection. -/
@[reassoc (attr := simp), stacks 017N "inverse first projection of the evaluated pullback functor"]
theorem functor.objIso.inv_fst (X : SimplicialObject C) :
    (functor.objIso (C := C) a b X).inv ≫
        (functor.fst (C := C) a b).app X =
      CategoryTheory.Limits.pullback.fst (precomp a X) (precomp b X) := sorry

/-- The inverse evaluated second projection agrees with the objectwise pullback projection. -/
@[reassoc (attr := simp), stacks 017N "inverse second projection of the evaluated pullback functor"]
theorem functor.objIso.inv_snd (X : SimplicialObject C) :
    (functor.objIso (C := C) a b X).inv ≫
        (functor.snd (C := C) a b).app X =
      CategoryTheory.Limits.pullback.snd (precomp a X) (precomp b X) := sorry

/-- Under the evaluation isomorphisms, the structure map of the pullback functor is
the canonical objectwise pullback map. -/
@[reassoc, stacks 017N "map of the evaluated internal-hom pullback functor"]
theorem functor.objIso.map {X Y : SimplicialObject C} (p : X ⟶ Y) :
    (functor (C := C) a b).map p ≫ (functor.objIso (C := C) a b Y).hom =
    (functor.objIso (C := C) a b X).hom ≫
      CategoryTheory.SimplicialObject.internalHom.pushout.pullback.map a b p := sorry

/-- The inverse evaluation comparisons are natural for maps of target simplicial objects. -/
@[reassoc, stacks 017N "inverse map of the evaluated internal-hom pullback functor"]
theorem functor.objIso.inv_map {X Y : SimplicialObject C} (p : X ⟶ Y) :
      (functor.objIso (C := C) a b X).inv ≫ (functor (C := C) a b).map p =
      CategoryTheory.SimplicialObject.internalHom.pushout.pullback.map a b p ≫
        (functor.objIso (C := C) a b Y).inv := sorry

end CategoryTheory.SimplicialObject.internalHom.pushout.pullback
