/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Variance

/-!
# Simplicial internal hom as a functor in the indexing object

For a fixed target simplicial object, this file bundles precomposition into a contravariant
index functor. It also bundles postcomposition by a target map into a natural transformation
between such index functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject

variable {C : Type uC} [Category.{vC} C]

section IndexFunctor

variable (T : SimplicialObject C)
variable [∀ U : SSet.{uS}, HasCopowers U C]
variable [∀ U : SSet.{uS}, HasInternalHom U T]

/-- For a fixed target simplicial object, internal hom is contravariantly functorial in the
indexing simplicial set. -/
@[stacks 017I "internal hom functor in the indexing variable"]
noncomputable def internalHom.indexFunctor : SSet.{uS}ᵒᵖ ⥤ SimplicialObject C where
  obj U := internalHom U.unop T
  map f := internalHom.precomp f.unop T
  map_id U := internalHom.precomp.id U.unop T
  map_comp f g := internalHom.precomp.comp g.unop f.unop T

/-- The fixed-target index functor evaluates to the corresponding internal mapping object. -/
@[simp, stacks 017I "internal hom index-functor object formula"]
theorem internalHom.indexFunctor.obj (U : SSet.{uS}ᵒᵖ) :
    (internalHom.indexFunctor T).obj U = internalHom U.unop T := sorry

/-- The fixed-target index functor acts by internal-hom precomposition. -/
@[simp, stacks 017I "internal hom index-functor map formula"]
theorem internalHom.indexFunctor.map {U V : SSet.{uS}ᵒᵖ} (f : U ⟶ V) :
    (internalHom.indexFunctor T).map f = internalHom.precomp f.unop T := sorry

end IndexFunctor

section TargetNaturalTransformation

variable {T T' : SimplicialObject C} (p : T ⟶ T')
variable [∀ U : SSet.{uS}, HasCopowers U C]
variable [∀ U : SSet.{uS}, HasInternalHom U T]
variable [∀ U : SSet.{uS}, HasInternalHom U T']

/-- A target morphism induces a natural transformation between fixed-target internal-hom
index functors by postcomposition. -/
@[stacks 017I "internal hom functoriality in the target variable"]
noncomputable def internalHom.postcomp.natTrans :
    internalHom.indexFunctor T ⟶ internalHom.indexFunctor T' where
  app U := internalHom.postcomp U.unop p
  naturality _ _ f := internalHom.interchange f.unop p

/-- The component of the target-variable natural transformation is internal-hom
postcomposition. -/
@[simp, stacks 017I "internal hom target natural-transformation component"]
theorem internalHom.postcomp.natTrans.app (U : SSet.{uS}ᵒᵖ) :
    (internalHom.postcomp.natTrans p).app U = internalHom.postcomp U.unop p := sorry

/-- The target natural transformation associated to an identity is the identity. -/
@[simp, stacks 017I "internal hom target natural-transformation identity"]
theorem internalHom.postcomp.natTrans.id (T : SimplicialObject C)
    [∀ U : SSet.{uS}, HasCopowers U C]
    [∀ U : SSet.{uS}, HasInternalHom U T] :
    internalHom.postcomp.natTrans (𝟙 T) = 𝟙 (internalHom.indexFunctor T) := sorry

/-- Target natural transformations preserve composition. -/
@[stacks 017I "internal hom target natural-transformation composition"]
theorem internalHom.postcomp.natTrans.comp {T'' : SimplicialObject C} (q : T' ⟶ T'')
    [∀ U : SSet.{uS}, HasInternalHom U T''] :
    internalHom.postcomp.natTrans (p ≫ q) =
      internalHom.postcomp.natTrans p ≫ internalHom.postcomp.natTrans q := sorry

end TargetNaturalTransformation

end CategoryTheory.SimplicialObject
