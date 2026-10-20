/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SymmetricAlgebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Commutative-ring-valued symmetric-algebra presheaves

This file bundles the sectionwise symmetric algebra of a module presheaf as a presheaf of
commutative rings, together with its canonical structure map from the base presheaf.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace PresheafOfModules.SymmetricAlgebra

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
variable (F : PresheafOfModules.{w} (RingPresheaf 𝒪))

/-- The commutative symmetric algebra of the module of sections over one object. -/
abbrev commRingObj (U : Cᵒᵖ) : CommRingCat.{w} :=
  CommRingCat.of (_root_.SymmetricAlgebra (𝒪.obj U) (sectionObj 𝒪 F U))

/-- The restriction morphism on sectionwise commutative symmetric algebras. -/
noncomputable abbrev commRingMap {U V : Cᵒᵖ} (i : U ⟶ V) :
    commRingObj 𝒪 F U ⟶ commRingObj 𝒪 F V :=
  CommRingCat.ofHom (restrictionRingHom 𝒪 F i)

/-- The restriction morphisms on sectionwise commutative symmetric algebras preserve
identities. -/
theorem commRingMap_id (U : Cᵒᵖ) :
    commRingMap 𝒪 F (𝟙 U) = 𝟙 (commRingObj 𝒪 F U) := sorry

/-- The restriction morphisms on sectionwise commutative symmetric algebras preserve
composition. -/
theorem commRingMap_comp {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    commRingMap 𝒪 F (i ≫ j) = commRingMap 𝒪 F i ≫ commRingMap 𝒪 F j := sorry

/-- The commutative-ring-valued sectionwise symmetric-algebra presheaf. -/
@[stacks 01CH "commutative-ring-valued symmetric-algebra presheaf"]
noncomputable def commRingPresheaf : Cᵒᵖ ⥤ CommRingCat.{w} where
  obj := commRingObj 𝒪 F
  map := commRingMap 𝒪 F
  map_id := commRingMap_id 𝒪 F
  map_comp := commRingMap_comp 𝒪 F

/-- The objectwise algebra map into the sectionwise commutative symmetric algebra. -/
abbrev commRingUnitApp (U : Cᵒᵖ) :
    𝒪.obj U ⟶ commRingObj 𝒪 F U :=
  CommRingCat.ofHom
    (algebraMap (𝒪.obj U) (_root_.SymmetricAlgebra (𝒪.obj U) (sectionObj 𝒪 F U)))

/-- The objectwise algebra maps into the symmetric algebras commute with restriction. -/
theorem commRingUnit_naturality {U V : Cᵒᵖ} (i : U ⟶ V) :
    𝒪.map i ≫ commRingUnitApp 𝒪 F V =
      commRingUnitApp 𝒪 F U ≫ (commRingPresheaf 𝒪 F).map i := sorry

/-- The canonical structure map from the base presheaf to its sectionwise commutative symmetric
algebra. -/
@[stacks 01CH "symmetric-algebra presheaf structure map"]
noncomputable def commRingUnit : 𝒪 ⟶ commRingPresheaf 𝒪 F where
  app := commRingUnitApp 𝒪 F
  naturality := fun {_ _} i ↦ commRingUnit_naturality 𝒪 F i

/-- Naturality of the identity comparison between the two additive symmetric-algebra
presheaves. -/
@[stacks 01CH "symmetric-algebra additive comparison naturality"]
theorem addCommGrpPresheafNatTrans_naturality {U V : Cᵒᵖ} (i : U ⟶ V) :
    ((commRingPresheaf 𝒪 F ⋙ forget₂ CommRingCat RingCat ⋙
        forget₂ RingCat AddCommGrpCat).map i) ≫ 𝟙 _ =
      𝟙 _ ≫ (presheaf 𝒪 F).presheaf.map i := sorry

/-- Naturality of the inverse identity comparison between the two additive symmetric-algebra
presheaves. -/
@[stacks 01CH "inverse symmetric-algebra additive comparison naturality"]
theorem addCommGrpPresheafInvNatTrans_naturality {U V : Cᵒᵖ} (i : U ⟶ V) :
    (presheaf 𝒪 F).presheaf.map i ≫ 𝟙 _ =
      𝟙 _ ≫ ((commRingPresheaf 𝒪 F ⋙ forget₂ CommRingCat RingCat ⋙
        forget₂ RingCat AddCommGrpCat).map i) := sorry

/-- The forward natural transformation forgetting multiplication from the symmetric algebra. -/
@[stacks 01CH "symmetric-algebra additive comparison natural transformation"]
noncomputable def addCommGrpPresheafNatTrans :
    commRingPresheaf 𝒪 F ⋙ forget₂ CommRingCat RingCat ⋙
        forget₂ RingCat AddCommGrpCat ⟶
      (presheaf 𝒪 F).presheaf where
  app _ := 𝟙 _
  naturality _ _ i := addCommGrpPresheafNatTrans_naturality 𝒪 F i

/-- The inverse natural transformation forgetting multiplication from the symmetric algebra. -/
@[stacks 01CH "inverse symmetric-algebra additive comparison natural transformation"]
noncomputable def addCommGrpPresheafInvNatTrans :
    (presheaf 𝒪 F).presheaf ⟶
      commRingPresheaf 𝒪 F ⋙ forget₂ CommRingCat RingCat ⋙
        forget₂ RingCat AddCommGrpCat where
  app _ := 𝟙 _
  naturality _ _ i := addCommGrpPresheafInvNatTrans_naturality 𝒪 F i

/-- A component of the forward symmetric-algebra additive comparison is the identity map. -/
@[simp, stacks 01CH "symmetric-algebra additive comparison component"]
theorem addCommGrpPresheafNatTrans_app (U : Cᵒᵖ) :
    (addCommGrpPresheafNatTrans 𝒪 F).app U = 𝟙 _ := sorry

/-- A component of the inverse symmetric-algebra additive comparison is the identity map. -/
@[simp, stacks 01CH "inverse symmetric-algebra additive comparison component"]
theorem addCommGrpPresheafInvNatTrans_app (U : Cᵒᵖ) :
    (addCommGrpPresheafInvNatTrans 𝒪 F).app U = 𝟙 _ := sorry

/-- The forward and inverse symmetric-algebra additive comparisons compose to the identity. -/
@[simp, stacks 01CH "symmetric-algebra additive comparison forward-inverse law"]
theorem addCommGrpPresheafNatTrans_hom_inv_id :
    addCommGrpPresheafNatTrans 𝒪 F ≫ addCommGrpPresheafInvNatTrans 𝒪 F = 𝟙 _ := sorry

/-- The inverse and forward symmetric-algebra additive comparisons compose to the identity. -/
@[simp, stacks 01CH "symmetric-algebra additive comparison inverse-forward law"]
theorem addCommGrpPresheafNatTrans_inv_hom_id :
    addCommGrpPresheafInvNatTrans 𝒪 F ≫ addCommGrpPresheafNatTrans 𝒪 F = 𝟙 _ := sorry

/-- Forgetting multiplication from the commutative-ring-valued symmetric-algebra presheaf
recovers the additive presheaf underlying the module-valued symmetric algebra. -/
@[stacks 01CH "symmetric-algebra additive presheaf comparison isomorphism"]
noncomputable def addCommGrpPresheafIso :
    commRingPresheaf 𝒪 F ⋙ forget₂ CommRingCat RingCat ⋙
        forget₂ RingCat AddCommGrpCat ≅
      (presheaf 𝒪 F).presheaf where
  hom := addCommGrpPresheafNatTrans 𝒪 F
  inv := addCommGrpPresheafInvNatTrans 𝒪 F
  hom_inv_id := addCommGrpPresheafNatTrans_hom_inv_id 𝒪 F
  inv_hom_id := addCommGrpPresheafNatTrans_inv_hom_id 𝒪 F

/-- The forward natural transformation of the symmetric-algebra additive comparison is explicit. -/
@[simp, stacks 01CH "symmetric-algebra additive comparison isomorphism hom"]
theorem addCommGrpPresheafIso_hom :
    (addCommGrpPresheafIso 𝒪 F).hom = addCommGrpPresheafNatTrans 𝒪 F := sorry

/-- The inverse natural transformation of the symmetric-algebra additive comparison is explicit. -/
@[simp, stacks 01CH "symmetric-algebra additive comparison isomorphism inverse"]
theorem addCommGrpPresheafIso_inv :
    (addCommGrpPresheafIso 𝒪 F).inv = addCommGrpPresheafInvNatTrans 𝒪 F := sorry

/-- Components of the symmetric-algebra additive comparison isomorphism are identity isomorphisms. -/
@[simp, stacks 01CH "symmetric-algebra additive comparison isomorphism component"]
theorem addCommGrpPresheafIso_app (U : Cᵒᵖ) :
    (addCommGrpPresheafIso 𝒪 F).app U = Iso.refl _ := sorry

/-- Forward components of the symmetric-algebra additive comparison isomorphism are identities. -/
@[simp, stacks 01CH "symmetric-algebra additive comparison hom component"]
theorem addCommGrpPresheafIso_hom_app (U : Cᵒᵖ) :
    (addCommGrpPresheafIso 𝒪 F).hom.app U = 𝟙 _ := sorry

/-- Inverse components of the symmetric-algebra additive comparison isomorphism are identities. -/
@[simp, stacks 01CH "symmetric-algebra additive comparison inverse component"]
theorem addCommGrpPresheafIso_inv_app (U : Cᵒᵖ) :
    (addCommGrpPresheafIso 𝒪 F).inv.app U = 𝟙 _ := sorry

end PresheafOfModules.SymmetricAlgebra
