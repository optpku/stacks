/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Functor.Target

/-!
# The simplicial internal-hom bifunctor

This file packages the two variance actions of simplicial internal hom as a curried bifunctor,
contravariant in the indexing simplicial set and covariant in the target simplicial object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject.internalHom

variable {C : Type uC} [Category.{vC} C]
variable [∀ U : SSet.{uS}, HasCopowers U C]
variable [∀ U : SSet.{uS}, HasInternalHoms U C]

section Construction

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- Identity compatibility for the indexing-variable maps used to construct the internal-hom
bifunctor. -/
@[stacks 017I "internal hom bifunctor identity"]
private theorem bifunctorMapId (U : SSet.{uS}ᵒᵖ) :
    precomp.natTrans (C := C) (𝟙 U).unop =
      𝟙 (targetFunctor (C := C) U.unop) := sorry

/-- Composition compatibility for the indexing-variable maps used to construct the
internal-hom bifunctor. -/
@[stacks 017I "internal hom bifunctor composition"]
private theorem bifunctorMapComp {U V W : SSet.{uS}ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    precomp.natTrans (C := C) (f ≫ g).unop =
      precomp.natTrans (C := C) f.unop ≫
        precomp.natTrans (C := C) g.unop := sorry

/-- Internal hom as a curried bifunctor, contravariant in the indexing simplicial set and
covariant in the target simplicial object. -/
@[stacks 017I "simplicial internal hom bifunctor"]
noncomputable def bifunctor :
    SSet.{uS}ᵒᵖ ⥤ (SimplicialObject C ⥤ SimplicialObject C) where
  obj U := targetFunctor (C := C) U.unop
  map f := precomp.natTrans (C := C) f.unop
  map_id U := bifunctorMapId U
  map_comp f g := bifunctorMapComp f g

end Construction

/-- Evaluating the internal-hom bifunctor in both variables gives the corresponding mapping
object. -/
@[simp, stacks 017I "internal hom bifunctor object formula"]
theorem bifunctor.obj_obj (U : SSet.{uS}ᵒᵖ) (T : SimplicialObject C) :
    ((bifunctor (C := C)).obj U).obj T = internalHom U.unop T := sorry

/-- The target-variable map of the internal-hom bifunctor is internal-hom postcomposition. -/
@[simp, stacks 017I "internal hom bifunctor target-map formula"]
theorem bifunctor.obj_map (U : SSet.{uS}ᵒᵖ)
    {T T' : SimplicialObject C} (p : T ⟶ T') :
    ((bifunctor (C := C)).obj U).map p = postcomp U.unop p := sorry

/-- The indexing-variable map of the internal-hom bifunctor is internal-hom
precomposition. -/
@[simp, stacks 017I "internal hom bifunctor index-map formula"]
theorem bifunctor.map_app {U V : SSet.{uS}ᵒᵖ}
    (f : U ⟶ V) (T : SimplicialObject C) :
    ((bifunctor (C := C)).map f).app T = precomp f.unop T := sorry

end CategoryTheory.SimplicialObject.internalHom
