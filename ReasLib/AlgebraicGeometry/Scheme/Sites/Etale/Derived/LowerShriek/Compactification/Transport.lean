/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.InverseImage.Isomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Module
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ExtensionByZero.LowerShriek

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Etale
namespace CompactificationTransport

-- Local instance justification: use the specified strong sheafification projection before
-- searching unrelated over-site families; this adds no mathematical hypothesis.
-- Local instance justification (search instability): Use the given strong sheafification projection before generic over-site search in this diagram context.
attribute [local instance 10000] HasSheafify.isRightAdjoint

/-- Cancel the actual ambient isomorphism in the interior triangle. -/
theorem inverseInteriorTriangle {X T T' : Scheme.{u}}
    (j : X ⟶ T) (j' : X ⟶ T') (e : T' ≅ T) (hj : j' ≫ e.hom = j) :
    j ≫ e.inv = j' := by
  rw [← hj, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- Cancel the actual ambient isomorphism in the structure triangle. -/
theorem inverseStructureTriangle {Y T T' : Scheme.{u}}
    (p : T ⟶ Y) (p' : T' ⟶ Y) (e : T' ≅ T) (hp : e.hom ≫ p = p') :
    e.inv ≫ p' = p := by
  rw [← hp, ← Category.assoc, e.inv_hom_id, Category.id_comp]

variable {X Y T T' : Scheme.{u}} (j : X ⟶ T) (p : T ⟶ Y)
  (j' : X ⟶ T') (p' : T' ⟶ Y) (e : T' ≅ T)
  (hj : j' ≫ e.hom = j) (hp : e.hom ≫ p = p')
  [sourceOpenImmersion : IsOpenImmersion j] [targetOpenImmersion : IsOpenImmersion j'] (Λ : Type u) [CommRing Λ]
  [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [X.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [X.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [Y.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasSheafify T.smallEtaleTopology AddCommGrpCat.{u}]
  [T.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [T.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ U : T.Etale, HasWeakSheafify (T.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify T'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasSheafify T'.smallEtaleTopology AddCommGrpCat.{u}]
  [T'.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [T'.smallEtaleTopology.PreservesSheafification
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ U : T'.Etale, HasWeakSheafify (T'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf T'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ, (etaleRestriction j).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}, (etaleRestriction j).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions (etaleRestriction j).op]
  [(etaleExtensionByZero j (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero j (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero j (ModuleCat.{u} Λ))]
  [targetRestrictionKanModule : ∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ, (etaleRestriction j').op.HasLeftKanExtension F]
  [targetRestrictionKanAdd : ∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}, (etaleRestriction j').op.HasLeftKanExtension F]
  [targetRestrictionPreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions (etaleRestriction j').op]
  [targetExtensionAdditive : (etaleExtensionByZero j' (ModuleCat.{u} Λ)).Additive]
  [targetExtensionLimits : PreservesFiniteLimits (etaleExtensionByZero j' (ModuleCat.{u} Λ))]
  [targetExtensionColimits : PreservesFiniteColimits (etaleExtensionByZero j' (ModuleCat.{u} Λ))]
  [∀ F : T.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ, (smallEtalePullback j).op.HasLeftKanExtension F]
  [targetInverseImageKan : ∀ F : T'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ, (smallEtalePullback j').op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ, (smallEtalePullback p).op.HasLeftKanExtension F]
  [targetPushforwardKan : ∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ, (smallEtalePullback p').op.HasLeftKanExtension F]

/-- Proper direct-image mate for the specified ambient isomorphism over the same base. -/
def ambientMate :
    (etaleDerivedPushforward p : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))) ⋙
        etaleModuleDerivedInverseImage (𝟙 Y) Λ ⟶
      etaleModuleDerivedInverseImage e.hom Λ ⋙ etaleDerivedPushforward p' := by
  -- Local instance justification (proof-local temporary data): Transfer the given Kan extensions using this ambient isomorphism's structure or interior triangle and the identity laws.
  letI : ∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (p' ≫ 𝟙 Y)).op.HasLeftKanExtension F :=
    fun F => by simpa only [Category.comp_id] using
      (inferInstance : (smallEtalePullback p').op.HasLeftKanExtension F)
  -- Local instance justification (proof-local temporary data): Transfer the given Kan extensions using this ambient isomorphism's structure or interior triangle and the identity laws.
  letI : ∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (e.hom ≫ p)).op.HasLeftKanExtension F :=
    fun F => by rw [hp]; infer_instance
  exact etaleDerivedPushforwardBaseChange p (𝟙 Y) p' e.hom
    (IsPullback.of_horiz_isIso ⟨hp.trans (Category.comp_id p').symm⟩) Λ

/-- Interior mate transported through the existing exact extension-by-zero identifications. -/
def interiorMate :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        etaleModuleDerivedInverseImage e.hom Λ ⟶
      etaleModuleDerivedInverseImage (𝟙 X) Λ ⋙
        (etaleExtensionByZero j' (ModuleCat.{u} Λ)).mapDerivedCategory := by
  -- Local instance justification (proof-local temporary data): Transfer the given Kan extensions using this ambient isomorphism's structure or interior triangle and the identity laws.
  letI : ∀ F : T.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (𝟙 X ≫ j)).op.HasLeftKanExtension F :=
    fun F => by simpa only [Category.id_comp] using
      (inferInstance : (smallEtalePullback j).op.HasLeftKanExtension F)
  -- Local instance justification (proof-local temporary data): Transfer the given Kan extensions using this ambient isomorphism's structure or interior triangle and the identity laws.
  letI : ∀ F : T.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (j' ≫ e.hom)).op.HasLeftKanExtension F :=
    fun F => by rw [hj]; infer_instance
  exact whiskerRight (extensionByZeroDerivedIsoLowerShriekModule j Λ).hom
      (etaleModuleDerivedInverseImage e.hom Λ) ≫
    lowerShriekModuleDerivedBaseChange j e.hom j' (𝟙 X)
      (IsPullback.of_horiz_isIso ⟨(Category.id_comp j).trans hj.symm⟩) Λ ≫
    whiskerLeft (etaleModuleDerivedInverseImage (𝟙 X) Λ)
      (extensionByZeroDerivedIsoLowerShriekModule j' Λ).inv

/-- Change the ambient of a compactification using the specified ambient and interior mates. -/
def modelComparison :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleDerivedPushforward p : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))) ⟶
      (etaleExtensionByZero j' (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleDerivedPushforward p' : (DerivedCategory (Sheaf T'.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))) :=
  let J := (etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategory
  let J' := (etaleExtensionByZero j' (ModuleCat.{u} Λ)).mapDerivedCategory
  let R : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) := etaleDerivedPushforward p
  let R' : (DerivedCategory (Sheaf T'.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) := etaleDerivedPushforward p'
  let E := etaleModuleDerivedInverseImage e.hom Λ
  let IY := etaleModuleDerivedInverseImage (𝟙 Y) Λ
  let IX := etaleModuleDerivedInverseImage (𝟙 X) Λ
  (Functor.rightUnitor (J ⋙ R)).inv ≫
    whiskerLeft (J ⋙ R) (derivedInverseImageIdentityIso Y Λ).inv ≫
    (Functor.associator J R IY).hom ≫
    whiskerLeft J (ambientMate p p' e hp Λ) ≫
    (Functor.associator J E R').inv ≫
    whiskerRight (interiorMate j j' e hj Λ) R' ≫
    (Functor.associator IX J' R').hom ≫
    whiskerRight (derivedInverseImageIdentityIso X Λ).hom (J' ⋙ R') ≫
    (Functor.leftUnitor (J' ⋙ R')).hom

/-- Forward and reverse ambient transport compose to the identity. -/
theorem modelComparison_hom_inv_id :
    modelComparison j p j' p' e hj hp Λ ≫ modelComparison j' p' j p e.symm
    (inverseInteriorTriangle j j' e hj) (inverseStructureTriangle p p' e hp) Λ = 𝟙 _ := sorry

/-- Reverse and forward ambient transport compose to the identity. -/
theorem modelComparison_inv_hom_id :
    modelComparison j' p' j p e.symm
    (inverseInteriorTriangle j j' e hj) (inverseStructureTriangle p p' e hp) Λ ≫ modelComparison j p j' p' e hj hp Λ = 𝟙 _ := sorry

/-- The model comparison has its actual reverse mate as inverse. -/
def modelIso :
    (etaleExtensionByZero j (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleDerivedPushforward p : (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))) ≅
      (etaleExtensionByZero j' (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleDerivedPushforward p' : (DerivedCategory (Sheaf T'.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))) where
  hom := modelComparison j p j' p' e hj hp Λ
  inv := modelComparison j' p' j p e.symm
    (inverseInteriorTriangle j j' e hj) (inverseStructureTriangle p p' e hp) Λ
  hom_inv_id := modelComparison_hom_inv_id j p j' p' e hj hp Λ
  inv_hom_id := modelComparison_inv_hom_id j p j' p' e hj hp Λ

/-- The forward map of the model isomorphism is the specified mate composite. -/
theorem modelIso_hom : (modelIso j p j' p' e hj hp Λ).hom =
    modelComparison j p j' p' e hj hp Λ := rfl

/-- The reverse map is built by the inverse ambient isomorphism and its two triangles. -/
theorem modelIso_inv : (modelIso j p j' p' e hj hp Λ).inv =
    modelComparison j' p' j p e.symm
      (inverseInteriorTriangle j j' e hj) (inverseStructureTriangle p p' e hp) Λ := rfl

end CompactificationTransport
end AlgebraicGeometry.Scheme.Etale
end
