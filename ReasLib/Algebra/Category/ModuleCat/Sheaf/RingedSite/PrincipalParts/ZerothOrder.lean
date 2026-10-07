module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts.ZerothOrder
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts.Construction

/-!
# Zeroth principal-parts sheaves

Sheafifying the presheaf-level zeroth-order comparison identifies zeroth principal parts with the
original module sheaf.  The comparison is natural in the module sheaf and therefore upgrades to
an isomorphism of endofunctors.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.PrincipalParts.ZerothOrder

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}

/-- Tag 0G3T: the zeroth principal-parts sheaf is canonically isomorphic to the original module
sheaf. -/
@[stacks 0G3T "zeroth principal-parts sheaf"]
noncomputable def iso (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    PrincipalParts.sheaf phi F 0 ≅ F :=
  (moduleSheafification O₂).mapIso
      (PresheafOfModules.PrincipalParts.ZerothOrder.iso phi.hom F.val) ≪≫
    moduleSheafificationValIso O₂ F

/-- The canonical projection from the zeroth principal-parts sheaf to the original module
sheaf. -/
noncomputable abbrev projection (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    PrincipalParts.sheaf phi F 0 ⟶ F :=
  (iso phi F).hom

/-- The canonical inverse from a module sheaf to its zeroth principal-parts sheaf. -/
noncomputable abbrev inclusion (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    F ⟶ PrincipalParts.sheaf phi F 0 :=
  (iso phi F).inv

section Naturality

variable {F G : ringedSiteModuleCategory J O₂}

/-- The zeroth principal-parts projection is natural in the module sheaf. -/
theorem projection_naturality (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    PrincipalParts.map phi 0 alpha ≫ projection phi G = projection phi F ≫ alpha := sorry

/-- The inverse zeroth principal-parts comparison is natural in the module sheaf. -/
@[stacks 0G3T "inverse zeroth principal-parts sheaf naturality"]
theorem inclusion_naturality (phi : O₁ ⟶ O₂) (alpha : F ⟶ G) :
    alpha ≫ inclusion phi G = inclusion phi F ≫ PrincipalParts.map phi 0 alpha := sorry

end Naturality

variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]

/-- The zeroth principal-parts projections form the forward natural transformation. -/
@[stacks 0G3T "forward zeroth principal-parts sheaf natural transformation"]
noncomputable def projectionNatTrans (phi : O₁ ⟶ O₂) :
    PrincipalParts.functor phi 0 ⟶ 𝟭 _ where
  app F := projection phi F
  naturality _ _ alpha := projection_naturality phi alpha

/-- The zeroth principal-parts inclusions form the inverse natural transformation. -/
@[stacks 0G3T "inverse zeroth principal-parts sheaf natural transformation"]
noncomputable def inclusionNatTrans (phi : O₁ ⟶ O₂) :
    𝟭 _ ⟶ PrincipalParts.functor phi 0 where
  app F := inclusion phi F
  naturality _ _ alpha := inclusion_naturality phi alpha

/-- A component of the forward zeroth principal-parts transformation is `projection`. -/
@[simp, stacks 0G3T "forward zeroth principal-parts sheaf transformation component"]
theorem projectionNatTrans_app (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    (projectionNatTrans phi).app F = projection phi F := sorry

/-- A component of the inverse zeroth principal-parts transformation is `inclusion`. -/
@[simp, stacks 0G3T "inverse zeroth principal-parts sheaf transformation component"]
theorem inclusionNatTrans_app (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    (inclusionNatTrans phi).app F = inclusion phi F := sorry

/-- The forward zeroth principal-parts transformation followed by its inverse is the identity. -/
@[simp, stacks 0G3T "zeroth principal-parts sheaf transformation forward-inverse law"]
theorem projectionNatTrans_hom_inv_id (phi : O₁ ⟶ O₂) :
    projectionNatTrans phi ≫ inclusionNatTrans phi = 𝟙 _ := sorry

/-- The inverse zeroth principal-parts transformation followed by its forward map is the identity.
-/
@[simp, stacks 0G3T "zeroth principal-parts sheaf transformation inverse-forward law"]
theorem projectionNatTrans_inv_hom_id (phi : O₁ ⟶ O₂) :
    inclusionNatTrans phi ≫ projectionNatTrans phi = 𝟙 _ := sorry

/-- Zeroth principal parts are naturally isomorphic to the identity endofunctor on module
sheaves. -/
@[stacks 0G3T "zeroth principal-parts sheaf natural isomorphism"]
noncomputable def natIso (phi : O₁ ⟶ O₂) : PrincipalParts.functor phi 0 ≅ 𝟭 _ :=
  { hom := projectionNatTrans phi
    inv := inclusionNatTrans phi
    hom_inv_id := projectionNatTrans_hom_inv_id phi
    inv_hom_id := projectionNatTrans_inv_hom_id phi }

/-- The forward natural transformation of `natIso` is explicit. -/
@[simp, stacks 0G3T "zeroth principal-parts sheaf natural isomorphism hom"]
theorem natIso_hom (phi : O₁ ⟶ O₂) :
    (natIso phi).hom = projectionNatTrans phi := sorry

/-- The inverse natural transformation of `natIso` is explicit. -/
@[simp, stacks 0G3T "zeroth principal-parts sheaf natural isomorphism inverse"]
theorem natIso_inv (phi : O₁ ⟶ O₂) :
    (natIso phi).inv = inclusionNatTrans phi := sorry

/-- A component of `natIso` is the objectwise zeroth principal-parts sheaf isomorphism. -/
@[simp, stacks 0G3T "zeroth principal-parts sheaf natural isomorphism component"]
theorem natIso_app (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    (natIso phi).app F = iso phi F := sorry

/-- The forward component of `natIso` is `projection`. -/
@[simp, stacks 0G3T "zeroth principal-parts sheaf natural isomorphism hom component"]
theorem natIso_hom_app (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    (natIso phi).hom.app F = projection phi F := sorry

/-- The inverse component of `natIso` is `inclusion`. -/
@[simp, stacks 0G3T "zeroth principal-parts sheaf natural isomorphism inverse component"]
theorem natIso_inv_app (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) :
    (natIso phi).inv.app F = inclusion phi F := sorry

end SheafOfModules.RingedSite.PrincipalParts.ZerothOrder
