/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Functor.Target
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Pushout.Naturality
public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Pushout.Pullback.Functor

/-!
@stack 017N

# Natural internal-hom comparisons for simplicial-set pushouts

This leaf owns the functor-category pullback statement and the canonical natural comparison,
explicit inverse, and natural isomorphism in the target simplicial object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe vC uC uS

namespace CategoryTheory.IsPushout

variable {C : Type uC} [Category.{vC} C]
variable {U V W P : SSet.{uS}} {a : U ⟶ V} {b : U ⟶ W}
variable {inl : V ⟶ P} {inr : W ⟶ P}

/-- Internal hom sends a simplicial-set pushout to a pullback naturally in the target
simplicial object. This is the functor-category owner of the natural comparison theorem. -/
@[stacks 017N "natural internal hom sends simplicial-set pushouts to pullbacks"]
theorem internalHomNat (h : IsPushout a b inl inr)
    [SimplicialObject.HasCopowers U C] [SimplicialObject.HasCopowers V C]
    [SimplicialObject.HasCopowers W C] [SimplicialObject.HasCopowers P C]
    [SimplicialObject.HasInternalHoms U C] [SimplicialObject.HasInternalHoms V C]
    [SimplicialObject.HasInternalHoms W C] [SimplicialObject.HasInternalHoms P C] :
    IsPullback
      (SimplicialObject.internalHom.precomp.natTrans (C := C) inl)
      (SimplicialObject.internalHom.precomp.natTrans (C := C) inr)
      (SimplicialObject.internalHom.precomp.natTrans (C := C) a)
      (SimplicialObject.internalHom.precomp.natTrans (C := C) b) := sorry

end CategoryTheory.IsPushout

namespace CategoryTheory.SimplicialObject.internalHom.pushout.comparison

variable {C : Type uC} [Category.{vC} C]
variable {U V W : SSet.{uS}} (a : U ⟶ V) (b : U ⟶ W)
variable [HasCopowers U C] [HasCopowers V C] [HasCopowers W C]
variable [HasCopowers (pushout a b) C]
variable [HasInternalHoms U C] [HasInternalHoms V C] [HasInternalHoms W C]
variable [HasInternalHoms (pushout a b) C]

/-- The two natural restriction maps from internal hom out of the pushout agree after
restriction to the source of the span. -/
@[stacks 017N "compatibility of the natural internal-hom restriction maps"]
theorem natTrans.condition :
    precomp.natTrans (C := C) (CategoryTheory.Limits.pushout.inl a b) ≫
        precomp.natTrans (C := C) a =
      precomp.natTrans (C := C) (CategoryTheory.Limits.pushout.inr a b) ≫
        precomp.natTrans (C := C) b := sorry

/-- The internal-hom pushout comparison, natural in the target simplicial object. -/
@[stacks 017N "natural internal-hom pushout comparison"]
noncomputable def natTrans :
    internalHom.targetFunctor (C := C) (pushout a b) ⟶
      pushout.pullback.functor (C := C) a b :=
  CategoryTheory.Limits.pullback.lift
    (precomp.natTrans (C := C) (CategoryTheory.Limits.pushout.inl a b))
    (precomp.natTrans (C := C) (CategoryTheory.Limits.pushout.inr a b))
    (natTrans.condition (C := C) a b)

/-- After evaluation identifies the functor-category pullback with the objectwise
pullback, each component of `natTrans` is the objectwise comparison. -/
@[reassoc, stacks 017N "component formula for the natural internal-hom comparison"]
theorem natTrans.app_objIso (X : SimplicialObject C) :
    (natTrans (C := C) a b).app X ≫
        (pushout.pullback.functor.objIso (C := C) a b X).hom =
      pushout.comparison a b X := sorry

namespace natInv

/-- Naturality of the inverse comparison assembled from the evaluated pullback
isomorphism and the explicit objectwise inverse. -/
@[stacks 017N "naturality of the inverse internal-hom pushout comparison"]
theorem naturality {X Y : SimplicialObject C} (p : X ⟶ Y) :
    (pushout.pullback.functor (C := C) a b).map p ≫
        ((pushout.pullback.functor.objIso (C := C) a b Y).hom ≫
          pushout.comparison.inv a b Y) =
      ((pushout.pullback.functor.objIso (C := C) a b X).hom ≫
          pushout.comparison.inv a b X) ≫
        (internalHom.targetFunctor (C := C) (pushout a b)).map p := sorry

end natInv

/-- The inverse natural comparison. Its components use the explicit inverse built from
copower descent, rather than extracting data from an `IsIso` proof. -/
@[stacks 017N "inverse natural internal-hom pushout comparison"]
noncomputable def natInv :
    pushout.pullback.functor (C := C) a b ⟶
      internalHom.targetFunctor (C := C) (pushout a b) where
  app X := (pushout.pullback.functor.objIso (C := C) a b X).hom ≫
    pushout.comparison.inv a b X
  naturality _ _ p := natInv.naturality (C := C) a b p

/-- The component of the inverse natural comparison is the evaluated objectwise inverse. -/
@[simp, stacks 017N "component formula for the inverse natural internal-hom comparison"]
theorem natInv.app (X : SimplicialObject C) :
    (natInv (C := C) a b).app X =
      (pushout.pullback.functor.objIso (C := C) a b X).hom ≫
        pushout.comparison.inv a b X := sorry

/-- The natural internal-hom pushout comparison is an isomorphism. -/
@[stacks 017N "natural internal-hom pushout comparison is an isomorphism", instance]
theorem natTrans.isIso : IsIso (natTrans (C := C) a b) := sorry

namespace natIso

/-- The natural comparison followed by its explicit inverse is the identity. -/
@[stacks 017N "forward-inverse law for the natural internal-hom comparison"]
theorem hom_inv_id : natTrans (C := C) a b ≫ natInv (C := C) a b = 𝟙 _ := sorry

/-- The explicit inverse followed by the natural comparison is the identity. -/
@[stacks 017N "inverse-forward law for the natural internal-hom comparison"]
theorem inv_hom_id : natInv (C := C) a b ≫ natTrans (C := C) a b = 𝟙 _ := sorry

end natIso

/-- The natural isomorphism identifying internal hom out of a simplicial-set
pushout with the pullback of the two internal-hom precomposition maps. -/
@[stacks 017N "internal hom out of a pushout as a natural pullback isomorphism"]
noncomputable def natIso :
    internalHom.targetFunctor (C := C) (pushout a b) ≅
      pushout.pullback.functor (C := C) a b where
  hom := natTrans (C := C) a b
  inv := natInv (C := C) a b
  hom_inv_id := natIso.hom_inv_id (C := C) a b
  inv_hom_id := natIso.inv_hom_id (C := C) a b

/-- The forward natural transformation of the natural pullback isomorphism is
the canonical natural comparison. -/
@[simp, stacks 017N "forward map of the natural internal-hom pushout isomorphism"]
theorem natIso.hom : (natIso (C := C) a b).hom = natTrans (C := C) a b := sorry

/-- The inverse natural transformation of the pullback isomorphism is the explicitly
constructed inverse comparison. -/
@[simp, stacks 017N "inverse map of the natural internal-hom pushout isomorphism"]
theorem natIso.inv : (natIso (C := C) a b).inv = natInv (C := C) a b := sorry

/-- Under objectwise evaluation, the forward component of the natural isomorphism is
the canonical objectwise comparison. -/
@[reassoc, stacks 017N "forward component of the natural internal-hom pushout isomorphism"]
theorem natIso.hom_app_objIso (X : SimplicialObject C) :
    (natIso (C := C) a b).hom.app X ≫
        (pushout.pullback.functor.objIso (C := C) a b X).hom =
      pushout.comparison a b X := sorry

/-- The inverse component of the natural pullback isomorphism is the evaluated explicit
objectwise inverse. -/
@[simp, stacks 017N "inverse component of the natural internal-hom pushout isomorphism"]
theorem natIso.inv_app (X : SimplicialObject C) :
    (natIso (C := C) a b).inv.app X =
      (pushout.pullback.functor.objIso (C := C) a b X).hom ≫
        pushout.comparison.inv a b X := sorry

end CategoryTheory.SimplicialObject.internalHom.pushout.comparison
