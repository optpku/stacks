/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.RepresentableBy.Variance

/-!
# Variance of chosen simplicial internal homs

This file specializes the choice-free variance API to the canonical representing objects
provided by `internalHom.representableBy`.
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
variable [HasInternalHom U T] [HasInternalHom V T]

/-- Precomposition by a simplicial-set morphism induces the corresponding morphism of
internal simplicial mapping objects. -/
@[stacks 017I "internal hom precomposition"]
abbrev internalHom.precomp : internalHom V T ⟶ internalHom U T :=
  internalHom.precompOf a (internalHom.representableBy U T)
    (internalHom.representableBy V T)

/-- Under the representing equivalences, postcomposition with `internalHom.precomp a T` is
precomposition by `copower.indexHom X a`. -/
@[stacks 017I "internal hom precomposition representation formula"]
theorem internalHom.precomp.homEquiv {X : SimplicialObject C}
    (f : X ⟶ internalHom V T) :
    internalHom.homEquiv U T X (f ≫ internalHom.precomp a T) =
      copower.indexHom X a ≫ internalHom.homEquiv V T X f := sorry

end Precomp

section PrecompIdentity

variable (U : SSet.{uS}) (T : SimplicialObject C)
variable [HasCopowers U C] [HasInternalHom U T]

/-- Precomposition by the identity simplicial-set morphism is the identity on the internal
mapping object. -/
@[simp, stacks 017I "internal hom precomposition identity"]
theorem internalHom.precomp.id : internalHom.precomp (𝟙 U) T = 𝟙 (internalHom U T) := sorry

end PrecompIdentity

section PrecompComposition

variable {U V W : SSet.{uS}} (a : U ⟶ V) (b : V ⟶ W) (T : SimplicialObject C)
variable [HasCopowers U C] [HasCopowers V C] [HasCopowers W C]
variable [HasInternalHom U T] [HasInternalHom V T] [HasInternalHom W T]

/-- Precomposition on internal mapping objects is contravariantly functorial in the indexing
simplicial set. -/
@[simp, stacks 017I "internal hom precomposition composition"]
theorem internalHom.precomp.comp :
    internalHom.precomp (a ≫ b) T =
      internalHom.precomp b T ≫ internalHom.precomp a T := sorry

end PrecompComposition

section Postcomp

variable (U : SSet.{uS}) {T T' : SimplicialObject C} (p : T ⟶ T')
variable [HasCopowers U C]
variable [HasInternalHom U T] [HasInternalHom U T']

/-- Postcomposition by a target morphism induces the corresponding morphism of internal
simplicial mapping objects. -/
@[stacks 017I "internal hom postcomposition"]
def internalHom.postcomp : internalHom U T ⟶ internalHom U T' :=
  internalHom.postcompOf p (internalHom.representableBy U T)
    (internalHom.representableBy U T')

/-- Under the representing equivalences, postcomposition with `internalHom.postcomp U p` is
postcomposition by `p`. -/
@[stacks 017I "internal hom postcomposition representation formula"]
theorem internalHom.postcomp.homEquiv {X : SimplicialObject C}
    (f : X ⟶ internalHom U T) :
    internalHom.homEquiv U T' X (f ≫ internalHom.postcomp U p) =
      internalHom.homEquiv U T X f ≫ p := sorry

end Postcomp

section PostcompIdentity

variable (U : SSet.{uS}) (T : SimplicialObject C)
variable [HasCopowers U C] [HasInternalHom U T]

/-- Postcomposition by the identity target morphism is the identity on the internal mapping
object. -/
@[simp, stacks 017I "internal hom postcomposition identity"]
theorem internalHom.postcomp.id : internalHom.postcomp U (𝟙 T) = 𝟙 (internalHom U T) := sorry

end PostcompIdentity

section PostcompComposition

variable (U : SSet.{uS}) {T T' T'' : SimplicialObject C} (p : T ⟶ T') (q : T' ⟶ T'')
variable [HasCopowers U C]
variable [HasInternalHom U T] [HasInternalHom U T'] [HasInternalHom U T'']

/-- Postcomposition on internal mapping objects is covariantly functorial in the target. -/
@[simp, stacks 017I "internal hom postcomposition composition"]
theorem internalHom.postcomp.comp :
    internalHom.postcomp U (p ≫ q) =
      internalHom.postcomp U p ≫ internalHom.postcomp U q := sorry

end PostcompComposition

section Interchange

variable {U V : SSet.{uS}} (a : U ⟶ V) {T T' : SimplicialObject C} (p : T ⟶ T')
variable [HasCopowers U C] [HasCopowers V C]
variable [HasInternalHom U T] [HasInternalHom V T]
variable [HasInternalHom U T'] [HasInternalHom V T']

/-- Precomposition in the indexing simplicial set commutes with postcomposition in the target
on internal mapping objects. -/
@[reassoc, stacks 017I "interchange for internal hom"]
theorem internalHom.interchange :
    internalHom.precomp a T ≫ internalHom.postcomp U p =
      internalHom.postcomp V p ≫ internalHom.precomp a T' := sorry

end Interchange

end CategoryTheory.SimplicialObject
