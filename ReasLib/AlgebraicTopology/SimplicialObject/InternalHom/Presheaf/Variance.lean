/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Representability
public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Index

/-!
# Variance of the simplicial internal-hom presheaf

This file owns the two variance actions on the presheaf represented by a simplicial internal
hom, before any representing object is chosen. Precomposition changes the indexing simplicial
set contravariantly, while postcomposition changes the target simplicial object covariantly.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject

variable {C : Type uC} [Category.{vC} C]

section Precomp

variable {U V : SSet.{uS}} (a : U ⟶ V) (T : SimplicialObject C)
variable [HasCopowers U C] [HasCopowers V C]

/-- Precomposition by an indexing map, before choosing representing objects. It sends a map
out of the `V`-indexed copower to its composite with the `U`-to-`V` reindexing morphism. -/
@[stacks 017I "precomposition on internal-hom presheaves"]
def internalHom.presheaf.precomp :
    internalHom.presheaf V T ⟶ internalHom.presheaf U T :=
  Functor.whiskerRight
    (NatTrans.op (copower.indexHom.natTrans (C := C) a)) (yoneda.obj T)

/-- Pointwise, presheaf precomposition is composition with the corresponding copower
reindexing morphism. -/
@[simp, stacks 017I "precomposition on internal-hom presheaves"]
theorem internalHom.presheaf.precomp.app
    {X : (SimplicialObject C)ᵒᵖ} (f : (internalHom.presheaf V T).obj X) :
    (internalHom.presheaf.precomp a T).app X f =
      copower.indexHom X.unop a ≫ f := sorry

/-- Presheaf precomposition by an identity is the identity natural transformation. -/
@[simp, stacks 017I "identity for internal-hom presheaf precomposition"]
theorem internalHom.presheaf.precomp.id (U : SSet.{uS}) (T : SimplicialObject C)
    [HasCopowers U C] :
    internalHom.presheaf.precomp (𝟙 U) T = 𝟙 (internalHom.presheaf U T) := sorry

/-- Presheaf precomposition is contravariantly compatible with composition of indexing maps. -/
@[simp, stacks 017I "composition for internal-hom presheaf precomposition"]
theorem internalHom.presheaf.precomp.comp
    {W : SSet.{uS}} (b : V ⟶ W) [HasCopowers W C] :
    internalHom.presheaf.precomp (a ≫ b) T =
      internalHom.presheaf.precomp b T ≫ internalHom.presheaf.precomp a T := sorry

end Precomp

section Postcomp

variable (U : SSet.{uS}) {T T' : SimplicialObject C} (p : T ⟶ T')
variable [HasCopowers U C]

/-- Postcomposition by a morphism of target simplicial objects, before choosing representing
objects. -/
@[stacks 017I "postcomposition on internal-hom presheaves"]
def internalHom.presheaf.postcomp :
    internalHom.presheaf U T ⟶ internalHom.presheaf U T' :=
  Functor.whiskerLeft (copower.functor U).op (yoneda.map p)

/-- Pointwise, presheaf postcomposition is composition with the target morphism. -/
@[simp, stacks 017I "postcomposition on internal-hom presheaves"]
theorem internalHom.presheaf.postcomp.app
    {X : (SimplicialObject C)ᵒᵖ} (f : (internalHom.presheaf U T).obj X) :
    (internalHom.presheaf.postcomp U p).app X f = f ≫ p := sorry

/-- Presheaf postcomposition by an identity is the identity natural transformation. -/
@[simp, stacks 017I "identity for internal-hom presheaf postcomposition"]
theorem internalHom.presheaf.postcomp.id (U : SSet.{uS}) (T : SimplicialObject C)
    [HasCopowers U C] :
    internalHom.presheaf.postcomp U (𝟙 T) = 𝟙 (internalHom.presheaf U T) := sorry

/-- Presheaf postcomposition is covariantly compatible with composition of target maps. -/
@[simp, stacks 017I "composition for internal-hom presheaf postcomposition"]
theorem internalHom.presheaf.postcomp.comp
    {T T' T'' : SimplicialObject C} (p : T ⟶ T') (q : T' ⟶ T'') :
    internalHom.presheaf.postcomp U (p ≫ q) =
      internalHom.presheaf.postcomp U p ≫ internalHom.presheaf.postcomp U q := sorry

end Postcomp

section Interchange

variable {U V : SSet.{uS}} (a : U ⟶ V) {T T' : SimplicialObject C} (p : T ⟶ T')
variable [HasCopowers U C] [HasCopowers V C]

/-- Precomposition in the indexing simplicial set commutes with postcomposition in the target
at the presheaf level. -/
@[reassoc, stacks 017I "interchange for internal-hom presheaves"]
theorem internalHom.presheaf.interchange :
    internalHom.presheaf.precomp a T ≫ internalHom.presheaf.postcomp U p =
      internalHom.presheaf.postcomp V p ≫ internalHom.presheaf.precomp a T' := sorry

end Interchange

end CategoryTheory.SimplicialObject
