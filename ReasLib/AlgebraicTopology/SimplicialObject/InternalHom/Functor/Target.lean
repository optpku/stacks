module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Variance

/-!
# Simplicial internal hom as a functor in the target

For a fixed indexing simplicial set, this file bundles postcomposition into a target functor.
It also bundles precomposition by an indexing map into a natural transformation between such
target functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject

variable {C : Type uC} [Category.{vC} C]

section TargetFunctor

variable (U : SSet.{uS}) [HasCopowers U C] [HasInternalHoms U C]

/-- For a fixed indexing simplicial set, internal hom is a covariant endofunctor in the
target simplicial object. -/
@[stacks 017I "internal hom functor in the target"]
noncomputable def internalHom.targetFunctor : SimplicialObject C ⥤ SimplicialObject C where
  obj T := internalHom U T
  map p := internalHom.postcomp U p
  map_id T := internalHom.postcomp.id U T
  map_comp p q := internalHom.postcomp.comp U p q

/-- The fixed-index internal-hom target functor evaluates to the corresponding mapping object. -/
@[simp, stacks 017I "internal hom target-functor object formula"]
theorem internalHom.targetFunctor.obj (T : SimplicialObject C) :
    (internalHom.targetFunctor U).obj T = internalHom U T := sorry

/-- The fixed-index internal-hom target functor acts by postcomposition. -/
@[simp, stacks 017I "internal hom target-functor map formula"]
theorem internalHom.targetFunctor.map {T T' : SimplicialObject C} (p : T ⟶ T') :
    (internalHom.targetFunctor U).map p = internalHom.postcomp U p := sorry

end TargetFunctor

section IndexNaturalTransformation

variable {U V : SSet.{uS}} (a : U ⟶ V)
variable [HasCopowers U C] [HasCopowers V C]
variable [HasInternalHoms U C] [HasInternalHoms V C]

/-- A map of indexing simplicial sets induces a natural transformation between fixed-index
internal-hom target functors in the reverse direction. -/
@[stacks 017I "internal hom functoriality in the indexing variable"]
noncomputable abbrev internalHom.precomp.natTrans :
    internalHom.targetFunctor (C := C) V ⟶ internalHom.targetFunctor (C := C) U where
  app T := internalHom.precomp a T
  naturality _ _ p := (internalHom.interchange a p).symm

/-- The component of the indexing-variable natural transformation is internal-hom
precomposition. -/
@[simp, stacks 017I "internal hom index natural-transformation component"]
theorem internalHom.precomp.natTrans.app (T : SimplicialObject C) :
    (internalHom.precomp.natTrans (C := C) a).app T = internalHom.precomp a T := sorry

/-- The indexing natural transformation associated to an identity is the identity. -/
@[simp, stacks 017I "internal hom index natural-transformation identity"]
theorem internalHom.precomp.natTrans.id (U : SSet.{uS})
    [HasCopowers U C] [HasInternalHoms U C] :
    internalHom.precomp.natTrans (C := C) (𝟙 U) =
      𝟙 (internalHom.targetFunctor (C := C) U) := sorry

/-- Indexing natural transformations reverse composition. -/
@[stacks 017I "internal hom index natural-transformation composition"]
theorem internalHom.precomp.natTrans.comp {W : SSet.{uS}} (b : V ⟶ W)
    [HasCopowers W C] [HasInternalHoms W C] :
    internalHom.precomp.natTrans (C := C) (a ≫ b) =
      internalHom.precomp.natTrans (C := C) b ≫
        internalHom.precomp.natTrans (C := C) a := sorry

end IndexNaturalTransformation

end CategoryTheory.SimplicialObject
