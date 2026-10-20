/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.InternalHom.Presheaf.Variance

/-!
# Variance between explicit simplicial internal-hom representations

This file transports the two variance actions on internal-hom presheaves to arbitrary explicit
representing objects. It is the choice-free data layer beneath the chosen `internalHom` API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe vC uC uS

namespace CategoryTheory.SimplicialObject

variable {C : Type uC} [Category.{vC} C]

section Precomp

variable {U V : SSet.{uS}} (a : U ⟶ V) {T : SimplicialObject C}
variable [HasCopowers U C] [HasCopowers V C]
variable {MU MV : SimplicialObject C}

/-- Precomposition between arbitrary explicit representing objects for the two internal-hom
presheaves. -/
@[stacks 017I "precomposition between explicit internal-hom representations"]
def internalHom.precompOf
    (RU : (internalHom.presheaf U T).RepresentableBy MU)
    (RV : (internalHom.presheaf V T).RepresentableBy MV) : MV ⟶ MU :=
  RV.map RU (internalHom.presheaf.precomp a T)

/-- Under arbitrary explicit representing equivalences, postcomposition with `precompOf` is
precomposition by the corresponding copower reindexing morphism. -/
@[stacks 017I "explicit internal-hom precomposition formula"]
theorem internalHom.precompOf.homEquiv
    (RU : (internalHom.presheaf U T).RepresentableBy MU)
    (RV : (internalHom.presheaf V T).RepresentableBy MV)
    {X : SimplicialObject C} (f : X ⟶ MV) :
    RU.homEquiv (f ≫ internalHom.precompOf a RU RV) =
      copower.indexHom X a ≫ RV.homEquiv f := sorry

/-- Explicit precomposition is natural under canonical changes of both representing objects;
this is the internal-hom specialization of `Functor.RepresentableBy.map_naturality`. -/
@[reassoc, stacks 017I "change of representation for internal-hom precomposition"]
theorem internalHom.precompOf.naturality
    {MU' MV' : SimplicialObject C}
    (RU : (internalHom.presheaf U T).RepresentableBy MU)
    (RU' : (internalHom.presheaf U T).RepresentableBy MU')
    (RV : (internalHom.presheaf V T).RepresentableBy MV)
    (RV' : (internalHom.presheaf V T).RepresentableBy MV') :
    (RV.uniqueUpToIso RV').hom ≫ internalHom.precompOf a RU' RV' =
      internalHom.precompOf a RU RV ≫ (RU.uniqueUpToIso RU').hom := sorry

/-- Explicit precomposition by an identity map is the identity of the representing object. -/
@[simp, stacks 017I "identity for explicit internal-hom precomposition"]
theorem internalHom.precompOf.id {U : SSet.{uS}} {T : SimplicialObject C}
    [HasCopowers U C] {M : SimplicialObject C}
    (R : (internalHom.presheaf U T).RepresentableBy M) :
    internalHom.precompOf (𝟙 U) R R = 𝟙 M := sorry

/-- Explicit precomposition is contravariantly compatible with composition of indexing maps. -/
@[simp, stacks 017I "composition for explicit internal-hom precomposition"]
theorem internalHom.precompOf.comp
    {W : SSet.{uS}} (b : V ⟶ W) [HasCopowers W C]
    {MW : SimplicialObject C}
    (RU : (internalHom.presheaf U T).RepresentableBy MU)
    (RV : (internalHom.presheaf V T).RepresentableBy MV)
    (RW : (internalHom.presheaf W T).RepresentableBy MW) :
    internalHom.precompOf (a ≫ b) RU RW =
      internalHom.precompOf b RV RW ≫ internalHom.precompOf a RU RV := sorry

end Precomp

section Postcomp

variable {U : SSet.{uS}} {T T' : SimplicialObject C} (p : T ⟶ T')
variable [HasCopowers U C] {M M' : SimplicialObject C}

/-- Postcomposition between arbitrary explicit representing objects for two internal-hom
presheaves with the same indexing simplicial set. -/
@[stacks 017I "postcomposition between explicit internal-hom representations"]
def internalHom.postcompOf
    (RT : (internalHom.presheaf U T).RepresentableBy M)
    (RT' : (internalHom.presheaf U T').RepresentableBy M') : M ⟶ M' :=
  RT.map RT' (internalHom.presheaf.postcomp U p)

/-- Under arbitrary explicit representing equivalences, postcomposition with `postcompOf`
corresponds to postcomposition by the target morphism. -/
@[stacks 017I "explicit internal-hom postcomposition formula"]
theorem internalHom.postcompOf.homEquiv
    (RT : (internalHom.presheaf U T).RepresentableBy M)
    (RT' : (internalHom.presheaf U T').RepresentableBy M')
    {X : SimplicialObject C} (f : X ⟶ M) :
    RT'.homEquiv (f ≫ internalHom.postcompOf p RT RT') = RT.homEquiv f ≫ p := sorry

/-- Explicit postcomposition is natural under canonical changes of both representing objects;
this is the internal-hom specialization of `Functor.RepresentableBy.map_naturality`. -/
@[reassoc, stacks 017I "change of representation for internal-hom postcomposition"]
theorem internalHom.postcompOf.naturality
    {N N' : SimplicialObject C}
    (RT : (internalHom.presheaf U T).RepresentableBy M)
    (RT₁ : (internalHom.presheaf U T).RepresentableBy N)
    (RT' : (internalHom.presheaf U T').RepresentableBy M')
    (RT₁' : (internalHom.presheaf U T').RepresentableBy N') :
    (RT.uniqueUpToIso RT₁).hom ≫ internalHom.postcompOf p RT₁ RT₁' =
      internalHom.postcompOf p RT RT' ≫ (RT'.uniqueUpToIso RT₁').hom := sorry

/-- Explicit postcomposition by an identity map is the identity of the representing object. -/
@[simp, stacks 017I "identity for explicit internal-hom postcomposition"]
theorem internalHom.postcompOf.id {T : SimplicialObject C} {M : SimplicialObject C}
    (R : (internalHom.presheaf U T).RepresentableBy M) :
    internalHom.postcompOf (𝟙 T) R R = 𝟙 M := sorry

/-- Explicit postcomposition is covariantly compatible with composition of target maps. -/
@[simp, stacks 017I "composition for explicit internal-hom postcomposition"]
theorem internalHom.postcompOf.comp
    {T T' T'' : SimplicialObject C} (p : T ⟶ T') (q : T' ⟶ T'')
    {M M' M'' : SimplicialObject C}
    (RT : (internalHom.presheaf U T).RepresentableBy M)
    (RT' : (internalHom.presheaf U T').RepresentableBy M')
    (RT'' : (internalHom.presheaf U T'').RepresentableBy M'') :
    internalHom.postcompOf (p ≫ q) RT RT'' =
      internalHom.postcompOf p RT RT' ≫ internalHom.postcompOf q RT' RT'' := sorry

end Postcomp

section Interchange

variable {U V : SSet.{uS}} (a : U ⟶ V) {T T' : SimplicialObject C} (p : T ⟶ T')
variable [HasCopowers U C] [HasCopowers V C]
variable {MUT MVT MUT' MVT' : SimplicialObject C}

/-- Precomposition and postcomposition commute between arbitrary explicit representing
objects. -/
@[reassoc, stacks 017I "interchange for explicit internal-hom representations"]
theorem internalHom.interchangeOf
    (RUT : (internalHom.presheaf U T).RepresentableBy MUT)
    (RVT : (internalHom.presheaf V T).RepresentableBy MVT)
    (RUT' : (internalHom.presheaf U T').RepresentableBy MUT')
    (RVT' : (internalHom.presheaf V T').RepresentableBy MVT') :
    internalHom.precompOf a RUT RVT ≫ internalHom.postcompOf p RUT RUT' =
      internalHom.postcompOf p RVT RVT' ≫ internalHom.precompOf a RUT' RVT' := sorry

end Interchange

end CategoryTheory.SimplicialObject
