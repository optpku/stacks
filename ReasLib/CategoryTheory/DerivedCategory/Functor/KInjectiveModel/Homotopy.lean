/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain

/-! # The K-injective universal model on the homotopy category

The unit descends the specified cochain unit through the native homotopy quotient.
Universal maps are the same actual cochain-model extension maps, with their input
comparison transported through the native quotient factorization isomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe w uC vC uD vD wC wD

namespace CategoryTheory.Functor.KInjectiveModel.Homotopy

variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable {D : Type uD} [Category.{vD} D] [Abelian D]
variable [HasDerivedCategory.{wD} D]
variable (F : C ⥤ D) [F.Additive]

variable [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{wC} C]

/-- The specified cochain unit expressed between functors precomposed by the homotopy quotient. -/
def unitOnCochains :
    HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Functor.Homotopy.toDerived F ⟶
      HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⋙ derived F :=
  (Functor.Homotopy.cochainIso F).hom ≫ KInjectiveModel.unit F ≫
    (isoWhiskerRight (DerivedCategory.quotientCompQhIso C) (derived F)).inv ≫
    (Functor.associator _ _ _).hom

/-- Native quotient descent preserves the actual augmentation components of the cochain unit. -/
def unit : Functor.Homotopy.toDerived F ⟶ DerivedCategory.Qh ⋙ derived F :=
  CategoryTheory.Quotient.natTransLift _ (unitOnCochains F)

/-- On a cochain representative, the descended unit has exactly the supplied component. -/
@[simp]
theorem unit_app_quotient (A : CochainComplex C ℤ) :
    (unit F).app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj A) =
      (unitOnCochains F).app A := rfl

/-- A homotopy-source extension supplies a cochain-source extension through native comparisons. -/
def extensionOnCochains
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (β : Functor.Homotopy.toDerived F ⟶ DerivedCategory.Qh ⋙ G) :
    ordinaryCochain F ⟶ DerivedCategory.Q ⋙ G :=
  (Functor.Homotopy.cochainIso F).inv ≫
    whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ)) β ≫
    (Functor.associator _ _ _).inv ≫
    (isoWhiskerRight (DerivedCategory.quotientCompQhIso C) G).hom

/-- The universal map is the actual cochain-model descent for the transported comparison. -/
def extensionDesc
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (β : Functor.Homotopy.toDerived F ⟶ DerivedCategory.Qh ⋙ G) : derived F ⟶ G :=
  KInjectiveModel.extensionDesc F G (extensionOnCochains F G β)

/-- The descended unit satisfies the universal comparison equation. -/
theorem extensionDesc_fac
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (β : Functor.Homotopy.toDerived F ⟶ DerivedCategory.Qh ⋙ G) :
    unit F ≫ whiskerLeft DerivedCategory.Qh (extensionDesc F G β) = β := by
  apply CategoryTheory.Quotient.natTrans_ext
  ext A
  let δ := KInjectiveModel.extensionDesc F G (extensionOnCochains F G β)
  have h := NatTrans.congr_app
    (KInjectiveModel.extensionDesc_fac F G (extensionOnCochains F G β)) A
  simp only [extensionOnCochains, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.comp_id, Category.id_comp, Category.assoc] at h
  change (KInjectiveModel.unit F).app A ≫ δ.app (DerivedCategory.Q.obj A) =
    (Functor.Homotopy.cochainIso F).inv.app A ≫
      β.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj A) ≫
      G.map ((DerivedCategory.quotientCompQhIso C).hom.app A) at h
  change (unitOnCochains F).app A ≫
    δ.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj A)) =
      β.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj A)
  simp only [unitOnCochains, NatTrans.comp_app, isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id, Category.id_comp, Category.assoc]
  erw [δ.naturality ((DerivedCategory.quotientCompQhIso C).inv.app A)]
  rw [← Category.assoc ((KInjectiveModel.unit F).app A), h]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← G.map_comp,
    Iso.hom_inv_id_app, Functor.map_id, Category.comp_id]
  erw [G.map_id]
  exact Category.comp_id _

/-- The initial-extension arrow stores the same actual universal map. -/
def initialExtensionDesc
    (E : Functor.LeftExtension (DerivedCategory.Qh (C := C)) (Functor.Homotopy.toDerived F)) :
    Functor.LeftExtension.mk (derived F) (unit F) ⟶ E :=
  StructuredArrow.homMk (extensionDesc F E.right E.hom)
    (extensionDesc_fac F E.right E.hom)

/-- Transport of the homotopy unit and a derived morphism recovers the cochain unit
and the same morphism. -/
theorem extensionOnCochains_unit
    (G : DerivedCategory C ⥤ DerivedCategory D) (γ : derived F ⟶ G) :
    extensionOnCochains F G (unit F ≫ whiskerLeft DerivedCategory.Qh γ) =
      KInjectiveModel.unit F ≫ whiskerLeft DerivedCategory.Q γ := by
  ext A
  simp only [extensionOnCochains, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, isoWhiskerRight_hom, Functor.whiskerRight_app,
    unit_app_quotient, Category.comp_id, Category.id_comp, Category.assoc]
  simp only [unitOnCochains, NatTrans.comp_app, Functor.associator_hom_app,
    isoWhiskerRight_inv, Functor.whiskerRight_app,
    Category.comp_id, Category.id_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [reassoc_of% γ.naturality ((DerivedCategory.quotientCompQhIso C).inv.app A)]
  simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id_app,
    Functor.map_id, Category.comp_id]

/-- The comparison with the descended augmentation determines the universal arrow. -/
theorem initialExtensionDesc_unique
    (E : Functor.LeftExtension (DerivedCategory.Qh (C := C)) (Functor.Homotopy.toDerived F))
    (m : Functor.LeftExtension.mk (derived F) (unit F) ⟶ E) :
    m = initialExtensionDesc F E := by
  let E' := Functor.LeftExtension.mk E.right (extensionOnCochains F E.right E.hom)
  have hm : KInjectiveModel.unit F ≫ whiskerLeft DerivedCategory.Q m.right =
      extensionOnCochains F E.right E.hom := by
    rw [← extensionOnCochains_unit]
    exact congrArg (extensionOnCochains F E.right) (StructuredArrow.w m)
  let m' : Functor.LeftExtension.mk (derived F) (KInjectiveModel.unit F) ⟶ E' :=
    StructuredArrow.homMk m.right hm
  apply StructuredArrow.hom_ext
  have h := congrArg (fun f : Functor.LeftExtension.mk (derived F)
      (KInjectiveModel.unit F) ⟶ E' => f.right)
    (KInjectiveModel.initialExtensionDesc_unique F E' m')
  exact h

/-- The actual homotopy-source universal witness. -/
def initialWitness :
    (Functor.LeftExtension.mk (derived F) (unit F)).IsUniversal :=
  IsInitial.ofUniqueHom (initialExtensionDesc F) (initialExtensionDesc_unique F)

/-- The existing model functor, equipped with the descended unit, is right derived. -/
instance isRightDerived :
    (derived F).IsRightDerivedFunctor (unit F)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) where
  isLeftKanExtension := { nonempty_isUniversal := ⟨initialWitness F⟩ }

/-- Native existence stores the constructed homotopy-source universal witness. -/
instance hasRightDerived :
    (Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  Functor.HasRightDerivedFunctor.mk' (RF := derived F) (α := unit F)

end CategoryTheory.Functor.KInjectiveModel.Homotopy
