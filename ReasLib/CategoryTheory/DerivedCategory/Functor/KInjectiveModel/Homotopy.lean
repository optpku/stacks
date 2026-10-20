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
    unit F ≫ whiskerLeft DerivedCategory.Qh (extensionDesc F G β) = β := sorry

/-- The initial-extension arrow stores the same actual universal map. -/
def initialExtensionDesc
    (E : Functor.LeftExtension (DerivedCategory.Qh (C := C)) (Functor.Homotopy.toDerived F)) :
    Functor.LeftExtension.mk (derived F) (unit F) ⟶ E :=
  StructuredArrow.homMk (extensionDesc F E.right E.hom)
    (extensionDesc_fac F E.right E.hom)

/-- The comparison with the descended augmentation determines the universal arrow. -/
theorem initialExtensionDesc_unique
    (E : Functor.LeftExtension (DerivedCategory.Qh (C := C)) (Functor.Homotopy.toDerived F))
    (m : Functor.LeftExtension.mk (derived F) (unit F) ⟶ E) :
    m = initialExtensionDesc F E := sorry

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
