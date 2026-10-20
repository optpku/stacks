/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PrincipalParts
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.PrincipalParts
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# The canonical principal-parts sheaf

For a morphism of commutative ring sheaves on a site, this file sheafifies the
sectionwise principal-parts presheaf.  The resulting sheaf is equipped with an explicit
corepresentation of the functor of bounded-order differential operators.

The construction is independent of a topological-space realization of the site.  All scalar
structures depending on the chosen ring-sheaf morphism remain confined to sectionwise data.

@stack 09CT
@stack 0G3S
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.PrincipalParts

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}

/-- The sectionwise principal-parts presheaf attached to a morphism of commutative ring sheaves. -/
abbrev presheaf (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ) :
    PresheafOfModules (ringSheaf J O₂).obj :=
  PresheafOfModules.PrincipalParts.presheaf phi.hom F.val k

/-- The canonical `k`-th principal-parts sheaf, obtained by sheafifying the sectionwise
principal-parts presheaf. -/
@[stacks 0G3T]
noncomputable abbrev sheaf
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ) :
    ringedSiteModuleCategory J O₂ :=
  (moduleSheafification O₂).obj (presheaf phi F k)

section Functoriality

variable {F G H : ringedSiteModuleCategory J O₂}

/-- The morphism on `k`-th principal-parts sheaves induced by a module-sheaf morphism. -/
noncomputable abbrev map (phi : O₁ ⟶ O₂) (k : ℕ) (alpha : F ⟶ G) :
    sheaf phi F k ⟶ sheaf phi G k :=
  (moduleSheafification O₂).map
    (PresheafOfModules.PrincipalParts.map phi.hom F.val k alpha.val)

/-- Principal-parts sheaf functoriality preserves identity morphisms. -/
@[simp]
theorem map_id (phi : O₁ ⟶ O₂) (k : ℕ) :
    map phi k (𝟙 F) = 𝟙 (sheaf phi F k) := sorry

/-- Principal-parts sheaf functoriality preserves composition. -/
@[simp]
theorem map_comp (phi : O₁ ⟶ O₂) (k : ℕ) (alpha : F ⟶ G) (beta : G ⟶ H) :
    map phi k (alpha ≫ beta) = map phi k alpha ≫ map phi k beta := sorry

/-- Principal parts of fixed order form an endofunctor on module sheaves over `O₂`. -/
noncomputable def functor (phi : O₁ ⟶ O₂) (k : ℕ) :
    ringedSiteModuleCategory J O₂ ⥤ ringedSiteModuleCategory J O₂ where
  obj F := sheaf phi F k
  map alpha := map phi k alpha
  map_id _ := map_id phi k
  map_comp alpha beta := map_comp phi k alpha beta

end Functoriality

namespace Presentation

/-- The target presheaf in the fixed-ring module-sheafification adjunction. -/
abbrev targetPresheaf (G : ringedSiteModuleCategory J O₂) :
    PresheafOfModules (ringSheaf J O₂).obj :=
  (moduleSheafificationRightAdjoint O₂).obj G

namespace Section

/-- Sectionwise differential operators of order at most `k`, with the scalar structures induced
by the explicitly chosen ring-sheaf morphism `phi` kept behind a single API boundary. -/
noncomputable abbrev operators
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂) (X : Cᵒᵖ) :=
  _root_.PrincipalParts.RingHom.operators
    (phi.hom.app X).hom (F.val.obj X) k (G.val.obj X)

/-- On one object of the site, morphisms from principal parts are linearly equivalent to
bounded-order differential operators. -/
noncomputable abbrev linearEquiv
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂) (X : Cᵒᵖ) :
    (PresheafOfModules.PrincipalParts.module phi.hom F.val k X ⟶
          ModuleCat.of (O₂.obj.obj X) (G.val.obj X)) ≃ₗ[O₂.obj.obj X]
        operators phi F k G X :=
  _root_.PrincipalParts.RingHom.representingLinearEquiv
    (phi.hom.app X).hom (F.val.obj X) k (G.val.obj X)

/-- The underlying equivalence of the sectionwise linear representing equivalence. -/
noncomputable abbrev homEquiv
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂) (X : Cᵒᵖ) :
    (PresheafOfModules.PrincipalParts.module phi.hom F.val k X ⟶
          ModuleCat.of (O₂.obj.obj X) (G.val.obj X)) ≃
        operators phi F k G X :=
  (linearEquiv phi F k G X).toEquiv

/-- A morphism from the principal-parts presentation defines the corresponding sectionwise
differential operator. -/
noncomputable abbrev toApp
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂)
    (beta : presheaf phi F k ⟶ targetPresheaf G) (X : Cᵒᵖ) :
    ((restrictionAlong phi).obj F).val.obj X ⟶
      ((restrictionAlong phi).obj G).val.obj X :=
  ModuleCat.ofHom
    (X := ((restrictionAlong phi).obj F).val.obj X)
    (Y := ((restrictionAlong phi).obj G).val.obj X)
    (ModuleCat.DifferentialOperators.toHom
      (homEquiv phi F k G X (beta.app X))).hom

/-- The sectionwise operators obtained from a presentation morphism are natural in the site
object. -/
theorem toApp_naturality
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂)
    (beta : presheaf phi F k ⟶ targetPresheaf G)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ((restrictionAlong phi).obj F).val.map f ≫
        (ModuleCat.restrictScalars (((ringSheaf J O₁).obj.map f).hom)).map
          (toApp phi F k G beta Y) =
      toApp phi F k G beta X ≫
        ((restrictionAlong phi).obj G).val.map f := sorry

end Section

/-- A morphism from the principal-parts presheaf to a sheaf target determines a morphism after
restriction of scalars. -/
noncomputable def toOperator
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂)
    (beta : presheaf phi F k ⟶ targetPresheaf G) :
    (restrictionAlong phi).obj F ⟶ (restrictionAlong phi).obj G :=
  ⟨{ app := Section.toApp phi F k G beta,
      naturality := Section.toApp_naturality phi F k G beta }⟩

/-- The differential operator reconstructed from a presentation morphism has order at most `k`. -/
theorem toOperator_mem
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂)
    (beta : presheaf phi F k ⟶ targetPresheaf G) :
    IsDifferentialOperatorOfOrder phi (toOperator phi F k G beta) k := sorry

namespace Section

/-- The bounded differential operator induced by a sheaf morphism, evaluated at one site
object. -/
noncomputable abbrev operator
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂)
    (D : DifferentialOperators.ofOrder phi F k G) (X : Cᵒᵖ) :
    operators phi F k G X :=
  ModuleCat.DifferentialOperators.ofHom
    ((DifferentialOperators.toHom D).val.app X)
    (DifferentialOperators.toHom_isOfOrder D X)

/-- A sheaf differential operator determines the corresponding map from the sectionwise
principal-parts module. -/
noncomputable abbrev ofApp
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂)
    (D : DifferentialOperators.ofOrder phi F k G) (X : Cᵒᵖ) :
    PresheafOfModules.PrincipalParts.module phi.hom F.val k X ⟶
      (targetPresheaf G).obj X :=
  (homEquiv phi F k G X).symm (operator phi F k G D X)

/-- The maps reconstructed from a sheaf differential operator are natural in the site object. -/
theorem ofApp_naturality
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂)
    (D : DifferentialOperators.ofOrder phi F k G)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    PresheafOfModules.PrincipalParts.restrictionMap phi.hom F.val k f ≫
        (ModuleCat.restrictScalars (((ringSheaf J O₂).obj.map f).hom)).map
          (ofApp phi F k G D Y) =
      ofApp phi F k G D X ≫
        (targetPresheaf G).map f := sorry

end Section

/-- A bounded sheaf differential operator determines a morphism from the principal-parts
presheaf to the target presheaf. -/
noncomputable def ofOperator
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂)
    (D : DifferentialOperators.ofOrder phi F k G) :
    presheaf phi F k ⟶ targetPresheaf G where
  app X := Section.ofApp phi F k G D X
  naturality f := Section.ofApp_naturality phi F k G D f

/-- Converting a principal-parts presentation to a differential operator and back is the
identity. -/
theorem left_inv
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂)
    (beta : presheaf phi F k ⟶ targetPresheaf G) :
    ofOperator phi F k G
        (DifferentialOperators.ofHom (toOperator phi F k G beta)
          (toOperator_mem phi F k G beta)) =
      beta := sorry

/-- Converting a bounded differential operator to a presentation morphism and back is the
identity. -/
theorem right_inv
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂)
    (D : DifferentialOperators.ofOrder phi F k G) :
    DifferentialOperators.ofHom
        (toOperator phi F k G (ofOperator phi F k G D))
        (toOperator_mem phi F k G (ofOperator phi F k G D)) = D := sorry

/-- Morphisms from the principal-parts presentation are equivalent to bounded-order
differential operators into the target sheaf. -/
noncomputable def homEquiv
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂) :
    (presheaf phi F k ⟶ targetPresheaf G) ≃ DifferentialOperators.ofOrder phi F k G where
  toFun beta := DifferentialOperators.ofHom (toOperator phi F k G beta)
    (toOperator_mem phi F k G beta)
  invFun := ofOperator phi F k G
  left_inv := left_inv phi F k G
  right_inv := right_inv phi F k G

/-- The presentation equivalence commutes with postcomposition in the target sheaf. -/
theorem homEquiv_naturality
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    {G G' : ringedSiteModuleCategory J O₂} (alpha : G ⟶ G')
    (beta : presheaf phi F k ⟶ targetPresheaf G) :
    homEquiv phi F k G'
        (beta ≫ (moduleSheafificationRightAdjoint O₂).map alpha) =
      (DifferentialOperators.functor phi F k).map alpha
        (homEquiv phi F k G beta) := sorry

end Presentation

/-- The sheafification adjunction and the sectionwise presentation combine to identify morphisms
from the canonical principal-parts sheaf with bounded-order differential operators. -/
noncomputable abbrev homEquiv
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂) :
    (sheaf phi F k ⟶ G) ≃ DifferentialOperators.ofOrder phi F k G :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf J O₂).obj)).trans
    (Presentation.homEquiv phi F k G)

/-- The canonical principal-parts representing equivalence preserves the additive structures on
the Hom group and the bounded-operator group. -/
noncomputable def homAddEquiv
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂) :
    (sheaf phi F k ⟶ G) ≃+ DifferentialOperators.ofOrder phi F k G where
  toEquiv := homEquiv phi F k G
  map_add' := sorry

/-- The sheaf-level representing equivalence is natural in the target sheaf. -/
theorem homEquiv_comp
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    {G G' : ringedSiteModuleCategory J O₂} (alpha : G ⟶ G')
    (f : sheaf phi F k ⟶ G) :
    homEquiv phi F k G' (f ≫ alpha) =
      (DifferentialOperators.functor phi F k).map alpha (homEquiv phi F k G f) := sorry

/-- The component of the additive representing isomorphism for the canonical principal-parts
sheaf. -/
noncomputable def representingIsoApp
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂) :
    (preadditiveCoyoneda.obj (Opposite.op (sheaf phi F k))).obj G ≅
      DifferentialOperators.group phi F k G :=
  (homAddEquiv phi F k G).toAddCommGrpIso

/-- The additive representing isomorphism is natural in the target module sheaf. -/
theorem representingIsoApp_naturality
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    {G G' : ringedSiteModuleCategory J O₂} (alpha : G ⟶ G') :
    (preadditiveCoyoneda.obj (Opposite.op (sheaf phi F k))).map alpha ≫
        (representingIsoApp phi F k G').hom =
      (representingIsoApp phi F k G).hom ≫
        (DifferentialOperators.groupFunctor phi F k).map alpha := sorry

/-- The inverse additive representing isomorphism is natural in the target module sheaf. -/
@[stacks 09CT "inverse additive principal-parts representation naturality"]
theorem representingIsoApp_inv_naturality
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    {G G' : ringedSiteModuleCategory J O₂} (alpha : G ⟶ G') :
    (DifferentialOperators.groupFunctor phi F k).map alpha ≫
        (representingIsoApp phi F k G').inv =
      (representingIsoApp phi F k G).inv ≫
        (preadditiveCoyoneda.obj (Opposite.op (sheaf phi F k))).map alpha := sorry

/-- The additive principal-parts representing maps form the forward natural transformation. -/
@[stacks 09CT "forward additive principal-parts representing natural transformation"]
noncomputable def representingNatTrans
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ) :
    preadditiveCoyoneda.obj (Opposite.op (sheaf phi F k)) ⟶
      DifferentialOperators.groupFunctor phi F k where
  app G := (representingIsoApp phi F k G).hom
  naturality _ _ alpha := representingIsoApp_naturality phi F k alpha

/-- The inverse additive principal-parts representing maps form the inverse natural
transformation. -/
@[stacks 09CT "inverse additive principal-parts representing natural transformation"]
noncomputable def representingInvNatTrans
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ) :
    DifferentialOperators.groupFunctor phi F k ⟶
      preadditiveCoyoneda.obj (Opposite.op (sheaf phi F k)) where
  app G := (representingIsoApp phi F k G).inv
  naturality _ _ alpha := representingIsoApp_inv_naturality phi F k alpha

/-- A component of the forward representing natural transformation is the objectwise additive
isomorphism. -/
@[simp, stacks 09CT "forward additive principal-parts representing component"]
theorem representingNatTrans_app
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂) :
    (representingNatTrans phi F k).app G = (representingIsoApp phi F k G).hom := sorry

/-- A component of the inverse representing natural transformation is the inverse objectwise
additive isomorphism. -/
@[simp, stacks 09CT "inverse additive principal-parts representing component"]
theorem representingInvNatTrans_app
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂) :
    (representingInvNatTrans phi F k).app G = (representingIsoApp phi F k G).inv := sorry

/-- The forward additive representing transformation followed by its inverse is the identity. -/
@[simp, stacks 09CT "additive principal-parts representing forward-inverse law"]
theorem representingNatTrans_hom_inv_id
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ) :
    representingNatTrans phi F k ≫ representingInvNatTrans phi F k = 𝟙 _ := sorry

/-- The inverse additive representing transformation followed by its forward map is the identity.
-/
@[simp, stacks 09CT "additive principal-parts representing inverse-forward law"]
theorem representingNatTrans_inv_hom_id
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ) :
    representingInvNatTrans phi F k ≫ representingNatTrans phi F k = 𝟙 _ := sorry

/-- The canonical principal-parts sheaf represents the additive-group-valued functor of bounded
differential operators. -/
@[stacks 09CT "additive principal-parts representation"]
noncomputable def representingIso
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ) :
    preadditiveCoyoneda.obj (Opposite.op (sheaf phi F k)) ≅
      DifferentialOperators.groupFunctor phi F k :=
  { hom := representingNatTrans phi F k
    inv := representingInvNatTrans phi F k
    hom_inv_id := representingNatTrans_hom_inv_id phi F k
    inv_hom_id := representingNatTrans_inv_hom_id phi F k }

/-- The forward natural transformation of `representingIso` is explicit. -/
@[simp, stacks 09CT "additive principal-parts representing natural isomorphism hom"]
theorem representingIso_hom
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ) :
    (representingIso phi F k).hom = representingNatTrans phi F k := sorry

/-- The inverse natural transformation of `representingIso` is explicit. -/
@[simp, stacks 09CT "additive principal-parts representing natural isomorphism inverse"]
theorem representingIso_inv
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ) :
    (representingIso phi F k).inv = representingInvNatTrans phi F k := sorry

/-- A component of `representingIso` is the objectwise additive representing isomorphism. -/
@[simp, stacks 09CT "additive principal-parts representing natural isomorphism component"]
theorem representingIso_app
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂) :
    (representingIso phi F k).app G = representingIsoApp phi F k G := sorry

/-- The canonical principal-parts sheaf corepresents order-`k` differential operators. -/
@[stacks 09CT "canonical principal-parts model"]
noncomputable def corepresentation
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ) :
    (DifferentialOperators.functor phi F k).CorepresentableBy (sheaf phi F k) where
  homEquiv {G} := homEquiv phi F k G
  homEquiv_comp {_ _} alpha f := homEquiv_comp phi F k alpha f

/-- The operator underlying the image of a morphism under the canonical representing
equivalence is obtained by postcomposing the universal principal-parts operator. -/
@[stacks 0G3S "canonical representing equivalence", stacks 09CT, simp]
theorem toHom_homEquiv
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    {G : ringedSiteModuleCategory J O₂} (f : sheaf phi F k ⟶ G) :
    DifferentialOperators.toHom (homEquiv phi F k G f) =
      universalOperator (corepresentation phi F k) ≫
        (restrictionAlong phi).map f := sorry

/-- The inverse of the canonical representing equivalence is universal descent from the
principal-parts sheaf. -/
@[stacks 0G3S "canonical universal descent", stacks 09CT, simp]
theorem homEquiv_symm_apply
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    {G : ringedSiteModuleCategory J O₂}
    (D : DifferentialOperators.ofOrder phi F k G) :
    (homEquiv phi F k G).symm D =
      desc (corepresentation phi F k) (DifferentialOperators.toHom D)
        (DifferentialOperators.toHom_isOfOrder D) := sorry

/-- The forward map of the objectwise additive representing isomorphism is the canonical
representing equivalence. -/
@[stacks 0G3S "objectwise forward representing map", stacks 09CT, simp]
theorem representingIsoApp_hom_apply
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂) (f : sheaf phi F k ⟶ G) :
    (representingIsoApp phi F k G).hom f = homEquiv phi F k G f := sorry

/-- The inverse map of the objectwise additive representing isomorphism is the inverse of the
canonical representing equivalence. -/
@[stacks 0G3S "objectwise inverse representing map", stacks 09CT, simp]
theorem representingIsoApp_inv_apply
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂)
    (D : DifferentialOperators.ofOrder phi F k G) :
    (representingIsoApp phi F k G).inv D =
      (homEquiv phi F k G).symm D := sorry

/-- The forward component of the natural additive representing isomorphism is the canonical
representing equivalence. -/
@[stacks 0G3S "forward natural representing map", stacks 09CT, simp]
theorem representingIso_hom_app
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂) (f : sheaf phi F k ⟶ G) :
    (representingIso phi F k).hom.app G f = homEquiv phi F k G f := sorry

/-- The inverse component of the natural additive representing isomorphism is universal descent
from the canonical principal-parts sheaf. -/
@[stacks 0G3S "inverse natural representing map", stacks 09CT, simp]
theorem representingIso_inv_app
    (phi : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ)
    (G : ringedSiteModuleCategory J O₂)
    (D : DifferentialOperators.ofOrder phi F k G) :
    (representingIso phi F k).inv.app G D =
      (homEquiv phi F k G).symm D := sorry

end SheafOfModules.RingedSite.PrincipalParts

namespace SheafOfModules.RingedSite.DifferentialOperators

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}

/-- Bounded differential operators from a fixed module sheaf are corepresentable by the canonical
sheafified principal-parts object. -/
@[stacks 09CT, stacks 0G3S, instance]
theorem isCorepresentable
    (φ : O₁ ⟶ O₂) (F : ringedSiteModuleCategory J O₂) (k : ℕ) :
    (functor φ F k).IsCorepresentable := sorry

end SheafOfModules.RingedSite.DifferentialOperators
