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

private theorem variance_homEquiv_map
    {F G : (SimplicialObject C)ᵒᵖ ⥤ Type vC} {M N X : SimplicialObject C}
    (RF : F.RepresentableBy M) (RG : G.RepresentableBy N)
    (α : F ⟶ G) (f : X ⟶ M) :
    RG.homEquiv (f ≫ RF.map RG α) = α.app (Opposite.op X) (RF.homEquiv f) := by
  unfold Functor.RepresentableBy.map
  rw [RG.homEquiv_comp, Equiv.apply_symm_apply, ← α.naturality_apply,
    ← RF.homEquiv_comp, Category.comp_id]

private theorem variance_homEquiv_comparison
    {F : (SimplicialObject C)ᵒᵖ ⥤ Type vC} {M N X : SimplicialObject C}
    (R : F.RepresentableBy M) (R' : F.RepresentableBy N) (f : X ⟶ M) :
    R'.homEquiv (f ≫ (R.uniqueUpToIso R').hom) = R.homEquiv f := by
  change R'.homEquiv (f ≫ R'.homEquiv.symm (R.homEquiv (𝟙 M))) = _
  rw [R'.homEquiv_comp, Equiv.apply_symm_apply, ← R.homEquiv_comp, Category.comp_id]

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
      copower.indexHom X a ≫ RV.homEquiv f := by
  exact variance_homEquiv_map RV RU (internalHom.presheaf.precomp a T) f

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
      internalHom.precompOf a RU RV ≫ (RU.uniqueUpToIso RU').hom := by
  have hV : RV'.homEquiv (RV.uniqueUpToIso RV').hom = RV.homEquiv (𝟙 MV) := by
    simpa only [Category.id_comp] using variance_homEquiv_comparison RV RV' (𝟙 MV)
  apply RU'.homEquiv.injective
  rw [internalHom.precompOf.homEquiv, hV, variance_homEquiv_comparison]
  simpa only [Category.id_comp] using
    (internalHom.precompOf.homEquiv a RU RV (𝟙 MV)).symm

/-- Explicit precomposition by an identity map is the identity of the representing object. -/
@[simp, stacks 017I "identity for explicit internal-hom precomposition"]
theorem internalHom.precompOf.id {U : SSet.{uS}} {T : SimplicialObject C}
    [HasCopowers U C] {M : SimplicialObject C}
    (R : (internalHom.presheaf U T).RepresentableBy M) :
    internalHom.precompOf (𝟙 U) R R = 𝟙 M := by
  apply R.homEquiv.injective
  rw [← Category.id_comp (internalHom.precompOf (𝟙 U) R R),
    internalHom.precompOf.homEquiv]
  exact (congrArg (fun k : copower U M ⟶ copower U M ↦ k ≫ R.homEquiv (𝟙 M))
    (Functor.indexedCoprod.indexHom.id M U)).trans (Category.id_comp _)

/-- Explicit precomposition is contravariantly compatible with composition of indexing maps. -/
@[simp, stacks 017I "composition for explicit internal-hom precomposition"]
theorem internalHom.precompOf.comp
    {W : SSet.{uS}} (b : V ⟶ W) [HasCopowers W C]
    {MW : SimplicialObject C}
    (RU : (internalHom.presheaf U T).RepresentableBy MU)
    (RV : (internalHom.presheaf V T).RepresentableBy MV)
    (RW : (internalHom.presheaf W T).RepresentableBy MW) :
    internalHom.precompOf (a ≫ b) RU RW =
      internalHom.precompOf b RV RW ≫ internalHom.precompOf a RU RV := by
  apply RU.homEquiv.injective
  rw [← Category.id_comp (internalHom.precompOf (a ≫ b) RU RW),
    internalHom.precompOf.homEquiv, internalHom.precompOf.homEquiv,
    ← Category.id_comp (internalHom.precompOf b RV RW), internalHom.precompOf.homEquiv]
  exact (congrArg (fun k : copower U MW ⟶ copower W MW ↦ k ≫ RW.homEquiv (𝟙 MW))
    (Functor.indexedCoprod.indexHom.comp MW a b)).trans (Category.assoc _ _ _)

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
    RT'.homEquiv (f ≫ internalHom.postcompOf p RT RT') = RT.homEquiv f ≫ p := by
  exact variance_homEquiv_map RT RT' (internalHom.presheaf.postcomp U p) f

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
      internalHom.postcompOf p RT RT' ≫ (RT'.uniqueUpToIso RT₁').hom := by
  have hT : RT₁.homEquiv (RT.uniqueUpToIso RT₁).hom = RT.homEquiv (𝟙 M) := by
    simpa only [Category.id_comp] using variance_homEquiv_comparison RT RT₁ (𝟙 M)
  apply RT₁'.homEquiv.injective
  rw [internalHom.postcompOf.homEquiv, hT, variance_homEquiv_comparison]
  simpa only [Category.id_comp] using
    (internalHom.postcompOf.homEquiv p RT RT' (𝟙 M)).symm

/-- Explicit postcomposition by an identity map is the identity of the representing object. -/
@[simp, stacks 017I "identity for explicit internal-hom postcomposition"]
theorem internalHom.postcompOf.id {T : SimplicialObject C} {M : SimplicialObject C}
    (R : (internalHom.presheaf U T).RepresentableBy M) :
    internalHom.postcompOf (𝟙 T) R R = 𝟙 M := by
  apply R.homEquiv.injective
  rw [← Category.id_comp (internalHom.postcompOf (𝟙 T) R R),
    internalHom.postcompOf.homEquiv, Category.comp_id]

/-- Explicit postcomposition is covariantly compatible with composition of target maps. -/
@[simp, stacks 017I "composition for explicit internal-hom postcomposition"]
theorem internalHom.postcompOf.comp
    {T T' T'' : SimplicialObject C} (p : T ⟶ T') (q : T' ⟶ T'')
    {M M' M'' : SimplicialObject C}
    (RT : (internalHom.presheaf U T).RepresentableBy M)
    (RT' : (internalHom.presheaf U T').RepresentableBy M')
    (RT'' : (internalHom.presheaf U T'').RepresentableBy M'') :
    internalHom.postcompOf (p ≫ q) RT RT'' =
      internalHom.postcompOf p RT RT' ≫ internalHom.postcompOf q RT' RT'' := by
  apply RT''.homEquiv.injective
  rw [← Category.id_comp (internalHom.postcompOf (p ≫ q) RT RT''),
    internalHom.postcompOf.homEquiv, internalHom.postcompOf.homEquiv,
    ← Category.id_comp (internalHom.postcompOf p RT RT'), internalHom.postcompOf.homEquiv,
    Category.assoc]

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
      internalHom.postcompOf p RVT RVT' ≫ internalHom.precompOf a RUT' RVT' := by
  apply RUT'.homEquiv.injective
  rw [internalHom.postcompOf.homEquiv, internalHom.precompOf.homEquiv,
    ← Category.id_comp (internalHom.precompOf a RUT RVT), internalHom.precompOf.homEquiv,
    ← Category.id_comp (internalHom.postcompOf p RVT RVT'), internalHom.postcompOf.homEquiv]
  exact Category.assoc _ _ _

end Interchange

end CategoryTheory.SimplicialObject
