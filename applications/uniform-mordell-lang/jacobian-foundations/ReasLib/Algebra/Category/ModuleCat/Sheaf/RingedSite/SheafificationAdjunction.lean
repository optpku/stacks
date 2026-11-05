module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sheafification
public import Mathlib.CategoryTheory.HomCongr

/-!
# Adjunction API for fixed-ring module sheafification

This leaf packages the reflective module-sheafification adjunction over a
fixed commutative ring sheaf on an arbitrary site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w z

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{z}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable (𝒪 : Sheaf J CommRingCat.{w})

/-- The right adjoint to fixed-ring module sheafification: forget the module sheaf and transport
along the identity of its underlying ring presheaf. -/
noncomputable abbrev moduleSheafificationRightAdjoint :
    ringedSiteModuleCategory.{u, v, z, w} J 𝒪 ⥤
      PresheafOfModules.{z} (ringSheaf J 𝒪).obj :=
  SheafOfModules.forget.{z} (ringSheaf J 𝒪) ⋙
    PresheafOfModules.restrictScalars.{z} (𝟙 (ringSheaf J 𝒪).obj)

/-- The canonical adjunction from module presheaves over a fixed ring sheaf to module sheaves. -/
noncomputable abbrev moduleSheafificationAdjunction :
    moduleSheafification 𝒪 ⊣ moduleSheafificationRightAdjoint 𝒪 :=
  PresheafOfModules.sheafificationAdjunction.{z} (𝟙 (ringSheaf J 𝒪).obj)

/-- The unit of the fixed-ring module-sheafification adjunction. -/
noncomputable abbrev moduleSheafificationUnit :
    𝟭 (PresheafOfModules.{z} (ringSheaf J 𝒪).obj) ⟶
      moduleSheafification 𝒪 ⋙ moduleSheafificationRightAdjoint 𝒪 :=
  (moduleSheafificationAdjunction 𝒪).unit

/-- The concrete counit natural transformation of fixed-ring module sheafification. -/
@[stacks 03L6 "fixed-ring module sheafification counit"]
noncomputable abbrev moduleSheafificationCounit :
    moduleSheafificationRightAdjoint 𝒪 ⋙ moduleSheafification 𝒪 ⟶
      𝟭 (ringedSiteModuleCategory.{u, v, z, w} J 𝒪) :=
  (moduleSheafificationAdjunction 𝒪).counit

/-- The named inverse natural transformation to the fixed-ring module-sheafification counit. -/
@[stacks 03L6 "fixed-ring module sheafification counit inverse"]
noncomputable def moduleSheafificationCounitInv :
    𝟭 (ringedSiteModuleCategory.{u, v, z, w} J 𝒪) ⟶
      moduleSheafificationRightAdjoint 𝒪 ⋙ moduleSheafification 𝒪 where
  app ℱ := inv ((moduleSheafificationCounit 𝒪).app ℱ)
  naturality _ _ _ := sorry

/-- The fixed-ring module-sheafification counit followed by its named inverse is the identity. -/
@[simp, stacks 03L6 "fixed-ring module sheafification counit forward-inverse law"]
theorem moduleSheafificationCounit_hom_inv_id :
    moduleSheafificationCounit 𝒪 ≫ moduleSheafificationCounitInv 𝒪 = 𝟙 _ := sorry

/-- The named inverse followed by the fixed-ring module-sheafification counit is the identity. -/
@[simp, stacks 03L6 "fixed-ring module sheafification counit inverse-forward law"]
theorem moduleSheafificationCounit_inv_hom_id :
    moduleSheafificationCounitInv 𝒪 ≫ moduleSheafificationCounit 𝒪 = 𝟙 _ := sorry

/-- The counit of fixed-ring module sheafification as a literal natural isomorphism with a
named inverse. -/
@[stacks 03L6 "fixed-ring module sheafification counit natural isomorphism"]
noncomputable def moduleSheafificationCounitIso :
    moduleSheafificationRightAdjoint 𝒪 ⋙ moduleSheafification 𝒪 ≅
      𝟭 (ringedSiteModuleCategory.{u, v, z, w} J 𝒪) :=
  { hom := moduleSheafificationCounit 𝒪
    inv := moduleSheafificationCounitInv 𝒪
    hom_inv_id := moduleSheafificationCounit_hom_inv_id 𝒪
    inv_hom_id := moduleSheafificationCounit_inv_hom_id 𝒪 }

/-- The forward transformation of the fixed-ring counit is the adjunction counit. -/
@[simp, stacks 03L6 "fixed-ring module sheafification counit natural isomorphism hom"]
theorem moduleSheafificationCounitIso_hom :
    (moduleSheafificationCounitIso 𝒪).hom = moduleSheafificationCounit 𝒪 := sorry

/-- The inverse transformation of the fixed-ring counit is the named inverse family. -/
@[simp, stacks 03L6 "fixed-ring module sheafification counit natural isomorphism inverse"]
theorem moduleSheafificationCounitIso_inv :
    (moduleSheafificationCounitIso 𝒪).inv = moduleSheafificationCounitInv 𝒪 := sorry

/-- The counit identifies the sheafification of the underlying identity-restricted presheaf of a
module sheaf with that module sheaf. -/
noncomputable abbrev moduleSheafificationCounitIsoApp
    (ℱ : ringedSiteModuleCategory.{u, v, z, w} J 𝒪) :
    (moduleSheafification 𝒪).obj
        ((moduleSheafificationRightAdjoint 𝒪).obj ℱ) ≅ ℱ :=
  (moduleSheafificationCounitIso 𝒪).app ℱ

/-- A component of the fixed-ring counit natural isomorphism is its named objectwise
isomorphism. -/
@[simp, stacks 03L6 "fixed-ring module sheafification counit component"]
theorem moduleSheafificationCounitIso_app
    (ℱ : ringedSiteModuleCategory.{u, v, z, w} J 𝒪) :
    (moduleSheafificationCounitIso 𝒪).app ℱ =
      moduleSheafificationCounitIsoApp 𝒪 ℱ := sorry

/-- The forward component of the fixed-ring counit natural isomorphism is the adjunction
counit component. -/
@[simp, stacks 03L6 "fixed-ring module sheafification counit hom component"]
theorem moduleSheafificationCounitIso_hom_app
    (ℱ : ringedSiteModuleCategory.{u, v, z, w} J 𝒪) :
    (moduleSheafificationCounitIso 𝒪).hom.app ℱ =
      (moduleSheafificationCounit 𝒪).app ℱ := sorry

/-- The inverse component of the fixed-ring counit natural isomorphism is the named inverse
component. -/
@[simp, stacks 03L6 "fixed-ring module sheafification counit inverse component"]
theorem moduleSheafificationCounitIso_inv_app
    (ℱ : ringedSiteModuleCategory.{u, v, z, w} J 𝒪) :
    (moduleSheafificationCounitIso 𝒪).inv.app ℱ =
      (moduleSheafificationCounitInv 𝒪).app ℱ := sorry

namespace ValRestriction

/-- Forgetting a module sheaf is naturally isomorphic to forgetting and then restricting
scalars along the identity of the underlying ring presheaf. -/
@[stacks 03L6 "underlying presheaf identity restriction"]
noncomputable def natIso :
    SheafOfModules.forget.{z} (ringSheaf J 𝒪) ≅
      moduleSheafificationRightAdjoint 𝒪 :=
  (SheafOfModules.forget.{z} (ringSheaf J 𝒪)).rightUnitor.symm ≪≫
    Functor.isoWhiskerLeft
      (SheafOfModules.forget.{z} (ringSheaf J 𝒪))
      (PresheafOfModules.Restriction.idIso (ringSheaf J 𝒪).obj)

/-- The forward natural transformation from the ordinary underlying module presheaf to its
identity-restricted presentation. -/
@[stacks 03L6 "underlying presheaf identity-restriction comparison"]
noncomputable def natTrans :
    SheafOfModules.forget.{z} (ringSheaf J 𝒪) ⟶
      moduleSheafificationRightAdjoint 𝒪 :=
  (natIso 𝒪).hom

/-- The inverse natural transformation from the identity-restricted presentation to the
ordinary underlying module presheaf. -/
@[stacks 03L6 "inverse underlying presheaf identity-restriction comparison"]
noncomputable def natTransInv :
    moduleSheafificationRightAdjoint 𝒪 ⟶
      SheafOfModules.forget.{z} (ringSheaf J 𝒪) :=
  (natIso 𝒪).inv

/-- Naturality of the underlying-presheaf identity-restriction comparison. -/
@[stacks 03L6 "underlying presheaf identity-restriction naturality"]
theorem natTrans_naturality
    {ℱ 𝒢 : ringedSiteModuleCategory.{u, v, z, w} J 𝒪} (f : ℱ ⟶ 𝒢) :
    f.val ≫ (natTrans 𝒪).app 𝒢 =
      (natTrans 𝒪).app ℱ ≫ (moduleSheafificationRightAdjoint 𝒪).map f := sorry

/-- Naturality of the inverse underlying-presheaf identity-restriction comparison. -/
@[stacks 03L6 "inverse underlying presheaf identity-restriction naturality"]
theorem natTransInv_naturality
    {ℱ 𝒢 : ringedSiteModuleCategory.{u, v, z, w} J 𝒪} (f : ℱ ⟶ 𝒢) :
    (moduleSheafificationRightAdjoint 𝒪).map f ≫ (natTransInv 𝒪).app 𝒢 =
      (natTransInv 𝒪).app ℱ ≫ f.val := sorry

/-- The underlying-presheaf comparison followed by its inverse is the identity. -/
@[simp, stacks 03L6 "underlying presheaf identity-restriction forward-inverse law"]
theorem natTrans_hom_inv_id :
    natTrans 𝒪 ≫ natTransInv 𝒪 = 𝟙 _ := sorry

/-- The inverse underlying-presheaf comparison followed by the comparison is the identity. -/
@[simp, stacks 03L6 "underlying presheaf identity-restriction inverse-forward law"]
theorem natTrans_inv_hom_id :
    natTransInv 𝒪 ≫ natTrans 𝒪 = 𝟙 _ := sorry

/-- The forward natural transformation of `ValRestriction.natIso`. -/
@[simp, stacks 03L6 "underlying presheaf identity-restriction isomorphism hom"]
theorem natIso_hom :
    (natIso 𝒪).hom = natTrans 𝒪 := sorry

/-- The inverse natural transformation of `ValRestriction.natIso`. -/
@[simp, stacks 03L6 "underlying presheaf identity-restriction isomorphism inverse"]
theorem natIso_inv :
    (natIso 𝒪).inv = natTransInv 𝒪 := sorry

end ValRestriction

/-- The underlying module presheaf of a module sheaf is canonically isomorphic to its
restriction of scalars along the identity ring-presheaf morphism. -/
noncomputable def valRestrictionIso
    (ℱ : ringedSiteModuleCategory.{u, v, z, w} J 𝒪) :
    ℱ.val ≅ (moduleSheafificationRightAdjoint 𝒪).obj ℱ :=
  PresheafOfModules.isoMk fun X =>
    (ModuleCat.restrictScalarsId (𝒪.obj.obj X)).symm.app (ℱ.val.obj X)

namespace ValRestriction

/-- A component of the functor-level identity-restriction isomorphism is the canonical
objectwise comparison. -/
@[simp, stacks 03L6 "underlying presheaf identity-restriction isomorphism component"]
theorem natIso_app
    (ℱ : ringedSiteModuleCategory.{u, v, z, w} J 𝒪) :
    (natIso 𝒪).app ℱ = valRestrictionIso 𝒪 ℱ := sorry

/-- A component of the forward identity-restriction comparison is the forward map of the
objectwise isomorphism. -/
@[simp, stacks 03L6 "underlying presheaf identity-restriction hom component"]
theorem natTrans_app
    (ℱ : ringedSiteModuleCategory.{u, v, z, w} J 𝒪) :
    (natTrans 𝒪).app ℱ = (valRestrictionIso 𝒪 ℱ).hom := sorry

/-- A component of the inverse identity-restriction comparison is the inverse map of the
objectwise isomorphism. -/
@[simp, stacks 03L6 "underlying presheaf identity-restriction inverse component"]
theorem natTransInv_app
    (ℱ : ringedSiteModuleCategory.{u, v, z, w} J 𝒪) :
    (natTransInv 𝒪).app ℱ = (valRestrictionIso 𝒪 ℱ).inv := sorry

end ValRestriction

/-- The universal property of fixed-ring module sheafification, expressed directly against the
ordinary underlying module presheaf of the target sheaf. -/
@[stacks 03L6 "hom equivalence for module sheafification"]
noncomputable def moduleSheafificationHomEquiv
    (P : PresheafOfModules.{z} (ringSheaf J 𝒪).obj)
    (H : ringedSiteModuleCategory.{u, v, z, w} J 𝒪) :
    ((moduleSheafification 𝒪).obj P ⟶ H) ≃ (P ⟶ H.val) :=
  ((moduleSheafificationAdjunction 𝒪).homEquiv P H).trans
    ((Iso.refl P).homCongr (valRestrictionIso 𝒪 H).symm)

/-- The sheafification unit, transported from the identity-restricted underlying presheaf back
to the ordinary underlying module presheaf. -/
noncomputable def moduleSheafificationUnitToVal
    (ℱ : PresheafOfModules.{z} (ringSheaf J 𝒪).obj) :
    ℱ ⟶ ((moduleSheafification 𝒪).obj ℱ).val :=
  (moduleSheafificationUnit 𝒪).app ℱ ≫
    (valRestrictionIso 𝒪 ((moduleSheafification 𝒪).obj ℱ)).inv

/-- Sheafifying the underlying presheaf of an existing module sheaf canonically recovers that
module sheaf. -/
noncomputable def moduleSheafificationValIso
    (ℱ : ringedSiteModuleCategory.{u, v, z, w} J 𝒪) :
    (moduleSheafification 𝒪).obj ℱ.val ≅ ℱ :=
  (moduleSheafification 𝒪).mapIso (valRestrictionIso 𝒪 ℱ) ≪≫
    moduleSheafificationCounitIsoApp 𝒪 ℱ

/-- Forgetting module structure after fixed-ring module sheafification agrees with sheafification
of the underlying additive presheaf. -/
noncomputable abbrev moduleSheafificationCompToSheaf :
    moduleSheafification 𝒪 ⋙ SheafOfModules.toSheaf.{z} (ringSheaf J 𝒪) ≅
      PresheafOfModules.toPresheaf.{z} (ringSheaf J 𝒪).obj ⋙
        presheafToSheaf J AddCommGrpCat.{z} :=
  PresheafOfModules.sheafificationCompToSheaf (𝟙 (ringSheaf J 𝒪).obj)

/-- Under strong sheafification, fixed-ring module sheafification is exact. -/
theorem moduleSheafificationExact [HasSheafify J AddCommGrpCat.{z}] :
    exactFunctor
      (PresheafOfModules.{z} (ringSheaf J 𝒪).obj)
      (ringedSiteModuleCategory.{u, v, z, w} J 𝒪)
      (moduleSheafification 𝒪) := sorry



end SheafOfModules.RingedSite
