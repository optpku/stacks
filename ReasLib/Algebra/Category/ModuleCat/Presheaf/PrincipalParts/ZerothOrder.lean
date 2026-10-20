/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts
public import ReasLib.Algebra.Module.PrincipalParts.RingHom.ZerothOrder

/-!
# Zeroth principal parts of module presheaves

Objectwise zeroth principal parts assemble into a presheaf canonically isomorphic to the original
module presheaf.  The comparison is natural in the module presheaf, hence gives an isomorphism of
endofunctors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace PresheafOfModules.PrincipalParts.ZerothOrder

variable {C : Type u} [Category.{v} C]
variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u v}}
variable (phi : O₁ ⟶ O₂) (F : PresheafOfModules (ringPresheaf O₂))

/-- The objectwise projection from zeroth principal parts to the original module presheaf. -/
noncomputable abbrev projectionApp (X : Cᵒᵖ) :
    PrincipalParts.module phi F 0 X ⟶ F.obj X :=
  _root_.PrincipalParts.RingHom.ZerothOrder.projection (phi.app X).hom (F.obj X)

/-- The objectwise zeroth projections commute with restriction maps. -/
theorem projectionApp_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    PrincipalParts.restrictionMap phi F 0 f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map
          (projectionApp phi F Y) =
      projectionApp phi F X ≫ F.map f := sorry

/-- The projection from the zeroth principal-parts presheaf to the original module presheaf. -/
noncomputable def projection : PrincipalParts.presheaf phi F 0 ⟶ F where
  app X := projectionApp phi F X
  naturality f := projectionApp_naturality phi F f

/-- The objectwise inverse from the original module presheaf to zeroth principal parts. -/
noncomputable abbrev inclusionApp (X : Cᵒᵖ) :
    F.obj X ⟶ PrincipalParts.module phi F 0 X :=
  _root_.PrincipalParts.RingHom.ZerothOrder.inclusion (phi.app X).hom (F.obj X)

/-- The objectwise inverses to the zeroth projections commute with restriction maps. -/
theorem inclusionApp_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    F.map f ≫
        (ModuleCat.restrictScalars ((ringPresheaf O₂).map f).hom).map
          (inclusionApp phi F Y) =
      inclusionApp phi F X ≫ PrincipalParts.restrictionMap phi F 0 f := sorry

/-- The inverse from the original module presheaf to its zeroth principal-parts presheaf. -/
noncomputable def inclusion : F ⟶ PrincipalParts.presheaf phi F 0 where
  app X := inclusionApp phi F X
  naturality f := inclusionApp_naturality phi F f

/-- The zeroth projection followed by its inverse is the identity. -/
@[simp]
theorem projection_inclusion : projection phi F ≫ inclusion phi F = 𝟙 _ := sorry

/-- The inverse followed by the zeroth projection is the identity. -/
@[simp]
theorem inclusion_projection : inclusion phi F ≫ projection phi F = 𝟙 _ := sorry

/-- Tag 0G3T: the zeroth principal-parts presheaf is canonically isomorphic to the original
module presheaf. -/
@[stacks 0G3T "zeroth principal parts presheaf"]
noncomputable def iso : PrincipalParts.presheaf phi F 0 ≅ F :=
  Iso.mk (projection phi F) (inclusion phi F)
    (projection_inclusion phi F) (inclusion_projection phi F)

section Naturality

variable {F G : PresheafOfModules (ringPresheaf O₂)}

/-- The zeroth projection is natural in the module-presheaf argument. -/
theorem projection_naturality (alpha : F ⟶ G) :
    PrincipalParts.map phi F 0 alpha ≫ projection phi G = projection phi F ≫ alpha := sorry

/-- The inverse zeroth comparison is natural in the module-presheaf argument. -/
theorem inclusion_naturality (alpha : F ⟶ G) :
    alpha ≫ inclusion phi G = inclusion phi F ≫ PrincipalParts.map phi F 0 alpha := sorry

end Naturality

/-- The zeroth principal-parts projections form a natural transformation to the identity
endofunctor. -/
@[stacks 0G3T "zeroth principal-parts projection natural transformation"]
noncomputable def natTrans : PrincipalParts.functor phi 0 ⟶ 𝟭 _ where
  app F := projection phi F
  naturality _ _ alpha := projection_naturality (phi := phi) alpha

/-- The inclusions into zeroth principal parts form the inverse natural transformation. -/
@[stacks 0G3T "zeroth principal-parts inverse natural transformation"]
noncomputable def invNatTrans : 𝟭 _ ⟶ PrincipalParts.functor phi 0 where
  app F := inclusion phi F
  naturality _ _ alpha := inclusion_naturality (phi := phi) alpha

/-- The zeroth projection natural transformation followed by its inverse is the identity. -/
@[simp, stacks 0G3T "zeroth principal-parts natural forward-inverse law"]
theorem natTrans_hom_inv_id : natTrans phi ≫ invNatTrans phi = 𝟙 _ := sorry

/-- The inverse zeroth principal-parts natural transformation followed by the projection is the
identity. -/
@[simp, stacks 0G3T "zeroth principal-parts natural inverse-forward law"]
theorem natTrans_inv_hom_id : invNatTrans phi ≫ natTrans phi = 𝟙 _ := sorry

/-- Zeroth principal parts are naturally isomorphic to the identity endofunctor on module
presheaves. -/
@[stacks 0G3T "zeroth principal-parts presheaf natural isomorphism"]
noncomputable def natIso : PrincipalParts.functor phi 0 ≅ 𝟭 _ :=
  { hom := natTrans phi
    inv := invNatTrans phi
    hom_inv_id := natTrans_hom_inv_id phi
    inv_hom_id := natTrans_inv_hom_id phi }

/-- A component of the zeroth principal-parts natural isomorphism is the objectwise isomorphism.
-/
@[simp, stacks 0G3T "zeroth principal-parts natural isomorphism component"]
theorem natIso_app (F : PresheafOfModules (ringPresheaf O₂)) :
    (natIso phi).app F = iso phi F := sorry

/-- The forward natural transformation of the zeroth principal-parts natural isomorphism is the
explicit projection transformation. -/
@[simp, stacks 0G3T "zeroth principal-parts natural isomorphism hom"]
theorem natIso_hom : (natIso phi).hom = natTrans phi := sorry

/-- The inverse natural transformation of the zeroth principal-parts natural isomorphism is the
explicit inclusion transformation. -/
@[simp, stacks 0G3T "zeroth principal-parts natural isomorphism inverse"]
theorem natIso_inv : (natIso phi).inv = invNatTrans phi := sorry

/-- The forward component of the zeroth principal-parts natural isomorphism is the objectwise
projection. -/
@[simp, stacks 0G3T "zeroth principal-parts natural isomorphism hom component"]
theorem natIso_hom_app (F : PresheafOfModules (ringPresheaf O₂)) :
    (natIso phi).hom.app F = projection phi F := sorry

/-- The inverse component of the zeroth principal-parts natural isomorphism is the objectwise
inclusion. -/
@[simp, stacks 0G3T "zeroth principal-parts natural isomorphism inverse component"]
theorem natIso_inv_app (F : PresheafOfModules (ringPresheaf O₂)) :
    (natIso phi).inv.app F = inclusion phi F := sorry

end PresheafOfModules.PrincipalParts.ZerothOrder
