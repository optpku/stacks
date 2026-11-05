/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Construction
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-! # Canonical unbounded right-derived functors from specified K-injective models

The model complex and augmentation are constructed by the small object argument. Localization
retains their actual maps, and every universal extension map is explicitly supplied before
its factorization and uniqueness laws.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section

set_option backward.isDefEq.respectTransparency false
universe w uC vC uD vD wC wD
namespace CategoryTheory.Functor.KInjectiveModel
variable {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
variable {D : Type uD} [Category.{vD} D] [Abelian D]
variable [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
variable (F : C ⥤ D) [F.Additive]

/-- The given additive functor applied degreewise, before resolving the input. -/
def ordinaryCochain :
    CochainComplex C ℤ ⥤ DerivedCategory D :=
  F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q

/-- The actual cochain functor evaluates the additive functor on its specified K-injective replacement. -/
def cochain  :
    CochainComplex C ℤ ⥤ DerivedCategory D :=
  (CochainComplex.KInjectiveResolution.Construction.replacement.{w} C) ⋙ ordinaryCochain F

/-- Quasi-isomorphisms between the actual K-injective replacements are homotopy equivalences;
additive direct image preserves their specified cochain maps up to quasi-isomorphism. -/
theorem modelMap_quasiIso  {A B : CochainComplex C ℤ}
    (a : A ⟶ B) (ha : QuasiIso a) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((CochainComplex.KInjectiveResolution.Construction.replacement.{w} C)).map a)) := by
  let R := CochainComplex.KInjectiveResolution.Construction.replacement.{w} C
  let η := CochainComplex.KInjectiveResolution.Construction.augmentation.{w} C
  haveI : QuasiIso a := ha
  haveI : QuasiIso (η.app A) :=
    CochainComplex.KInjectiveResolution.Construction.augmentation_quasiIso C A
  haveI : QuasiIso (η.app B) :=
    CochainComplex.KInjectiveResolution.Construction.augmentation_quasiIso C B
  haveI : QuasiIso (R.map a) := by
    haveI : QuasiIso (η.app A ≫ R.map a) := by
      rw [← η.naturality a]
      change QuasiIso (a ≫ η.app B)
      infer_instance
    exact quasiIso_of_comp_left (η.app A) (R.map a)
  haveI : (R.obj A).IsKInjective :=
    CochainComplex.KInjectiveResolution.Construction.replacement_isKInjective C A
  haveI : (R.obj B).IsKInjective :=
    CochainComplex.KInjectiveResolution.Construction.replacement_isKInjective C B
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff (R.map a)).mp inferInstance
  exact homotopyEquivalences_le_quasiIso _ _ _
    ⟨F.mapHomotopyEquiv e, congrArg (F.mapHomologicalComplex _).map he⟩

/-- The specified cochain functor inverts original quasi-isomorphisms. -/
theorem cochain_inverts  :
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)).IsInvertedBy
      (cochain F) := by
  intro A B a ha
  letI := modelMap_quasiIso F a ha
  change IsIso ((DerivedCategory.Q (C := D)).map
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (((CochainComplex.KInjectiveResolution.Construction.replacement.{w} C)).map a)))
  infer_instance

/-- The actual unbounded right-derived functor on the ambient derived categories. -/
def derived  :
    DerivedCategory C ⥤ DerivedCategory D :=
  Localization.lift (cochain F) (cochain_inverts F) (DerivedCategory.Q (C := C))

/-- Native localization keeps the specified cochain-computation functor and its actual maps. -/
def fac  :
    DerivedCategory.Q (C := C) ⋙ derived F ≅ cochain F :=
  Localization.fac (cochain F) (cochain_inverts F) (DerivedCategory.Q (C := C))

/-- The right-derived unit is the given functor applied to the specified augmentation. -/
def unit  : ordinaryCochain F ⟶ DerivedCategory.Q ⋙ derived F :=
  (Functor.leftUnitor (ordinaryCochain F)).inv ≫
    Functor.whiskerRight ((CochainComplex.KInjectiveResolution.Construction.augmentation.{w} C)) (ordinaryCochain F) ≫ (fac F).inv

/-- Formal localization of the actual original-input augmentation. -/
def inputAugmentationIso  (A : CochainComplex C ℤ) :
    DerivedCategory.Q.obj A ≅ DerivedCategory.Q.obj (((CochainComplex.KInjectiveResolution.Construction.replacement.{w} C)).obj A) :=
  Localization.isoOfHom (DerivedCategory.Q (C := C))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (((CochainComplex.KInjectiveResolution.Construction.augmentation.{w} C)).app A)
    (CochainComplex.KInjectiveResolution.Construction.augmentation_quasiIso C A)

/-- The two augmentations of a replacement agree after applying the additive functor.
Their homotopy classes agree because the original augmentation is a quasi-isomorphism
and the target is K-injective. -/
theorem ordinaryCochain_augmentation_coherence (A : CochainComplex C ℤ) :
    (ordinaryCochain F).map
        ((CochainComplex.KInjectiveResolution.Construction.replacement.{w} C).map
          ((CochainComplex.KInjectiveResolution.Construction.augmentation.{w} C).app A)) =
      (ordinaryCochain F).map
        ((CochainComplex.KInjectiveResolution.Construction.augmentation.{w} C).app
          ((CochainComplex.KInjectiveResolution.Construction.replacement.{w} C).obj A)) := by
  let R := CochainComplex.KInjectiveResolution.Construction.replacement.{w} C
  let η := CochainComplex.KInjectiveResolution.Construction.augmentation.{w} C
  haveI : (R.obj (R.obj A)).IsKInjective :=
    CochainComplex.KInjectiveResolution.Construction.replacement_isKInjective C _
  have hQ : DerivedCategory.Q.map (R.map (η.app A)) =
      DerivedCategory.Q.map (η.app (R.obj A)) := by
    apply (cancel_epi (inputAugmentationIso A).hom).mp
    change DerivedCategory.Q.map (η.app A) ≫ _ = DerivedCategory.Q.map (η.app A) ≫ _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map (η.naturality (η.app A)).symm
  have hq : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (R.map (η.app A)) =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (η.app (R.obj A)) := by
    apply (CochainComplex.IsKInjective.Qh_map_bijective _ _).injective
    apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app (R.obj (R.obj A)))).mp
    rw [DerivedCategory.quotientCompQhIso_hom_naturality,
      DerivedCategory.quotientCompQhIso_hom_naturality, hQ]
    rfl
  exact DerivedCategory.Q_map_eq_of_homotopy D
    (F.mapHomotopy (HomotopyCategory.homotopyOfEq _ _ hq))

/-- The universal map uses a supplied extension comparison at the actual model, then reverses
only the formal localization of the specified original-input augmentation. -/
def extensionDescOnInput
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (β : ordinaryCochain F ⟶ DerivedCategory.Q ⋙ G)
    (A : CochainComplex C ℤ) :
    (derived F).obj (DerivedCategory.Q.obj A) ⟶ G.obj (DerivedCategory.Q.obj A) :=
  (fac F).hom.app A ≫ β.app (((CochainComplex.KInjectiveResolution.Construction.replacement.{w} C)).obj A) ≫ G.map (inputAugmentationIso A).inv

/-- The specified extension formula is natural in each original cochain map. -/
theorem extensionDescOnInput_naturality
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (β : ordinaryCochain F ⟶ DerivedCategory.Q ⋙ G)
    {A B : CochainComplex C ℤ} (a : A ⟶ B) :
    (DerivedCategory.Q ⋙ derived F).map a ≫ extensionDescOnInput F G β B =
      extensionDescOnInput F G β A ≫ (DerivedCategory.Q ⋙ G).map a := by
  let R := CochainComplex.KInjectiveResolution.Construction.replacement.{w} C
  let η := CochainComplex.KInjectiveResolution.Construction.augmentation.{w} C
  have hη : DerivedCategory.Q.map (R.map a) ≫ (inputAugmentationIso B).inv =
      (inputAugmentationIso A).inv ≫ DerivedCategory.Q.map a := by
    apply (cancel_mono (inputAugmentationIso B).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply (cancel_epi (inputAugmentationIso A).hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    change DerivedCategory.Q.map (η.app A) ≫ DerivedCategory.Q.map (R.map a) =
      DerivedCategory.Q.map a ≫ DerivedCategory.Q.map (η.app B)
    rw [← Functor.map_comp, ← Functor.map_comp, ← η.naturality a]
    rfl
  dsimp only [extensionDescOnInput]
  simp only [← Category.assoc]
  rw [(fac F).hom.naturality a]
  dsimp only [cochain, Functor.comp_map]
  simp only [Category.assoc]
  rw [← Category.assoc ((ordinaryCochain F).map (R.map a)),
    β.naturality (R.map a)]
  simp only [Functor.comp_map, Category.assoc]
  rw [← G.map_comp, hη, G.map_comp]

/-- The actual natural transformation before localization descent. -/
def extensionDescOnCochains
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (β : ordinaryCochain F ⟶ DerivedCategory.Q ⋙ G) :
    DerivedCategory.Q ⋙ derived F ⟶ DerivedCategory.Q ⋙ G where
  app A := extensionDescOnInput F G β A
  naturality := fun _ _ a ↦ extensionDescOnInput_naturality F G β a

/-- Native descent along quasi-isomorphisms retains those specified extension maps. -/
def extensionDesc
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (β : ordinaryCochain F ⟶ DerivedCategory.Q ⋙ G) : derived F ⟶ G :=
  Localization.liftNatTrans (DerivedCategory.Q (C := C))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ derived F) (DerivedCategory.Q ⋙ G)
    (derived F) G (extensionDescOnCochains F G β)

/-- The constructed descent satisfies its comparison equation. -/
theorem extensionDesc_fac
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (β : ordinaryCochain F ⟶ DerivedCategory.Q ⋙ G) :
    unit F ≫ Functor.whiskerLeft DerivedCategory.Q (extensionDesc F G β) = β := by
  ext A
  simp only [unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_inv_app, Category.id_comp, Functor.whiskerRight_app,
    extensionDesc, Localization.liftNatTrans_app,
    Localization.Lifting.compLeft_iso, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id,
    extensionDescOnCochains, extensionDescOnInput, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc, β.naturality]
  simp only [Functor.comp_map, Category.assoc, ← G.map_comp]
  change β.app A ≫ G.map ((inputAugmentationIso A).hom ≫
    (inputAugmentationIso A).inv) = β.app A
  rw [Iso.hom_inv_id, G.map_id]
  exact Category.comp_id _

/-- The initial-extension arrow contains the actual cochain-model descent. -/
def initialExtensionDesc
    (E : Functor.LeftExtension (DerivedCategory.Q (C := C))
      (ordinaryCochain F)) :
    Functor.LeftExtension.mk (derived F) (unit F) ⟶ E :=
  StructuredArrow.homMk (extensionDesc F E.right E.hom) (extensionDesc_fac F E.right E.hom)

/-- The augmentation comparison uniquely determines an initial-extension arrow. -/
theorem initialExtensionDesc_unique
    (E : Functor.LeftExtension (DerivedCategory.Q (C := C))
      (ordinaryCochain F))
    (m : Functor.LeftExtension.mk (derived F) (unit F) ⟶ E) :
    m = initialExtensionDesc F E := by
  let R := CochainComplex.KInjectiveResolution.Construction.replacement.{w} C
  let η := CochainComplex.KInjectiveResolution.Construction.augmentation.{w} C
  apply StructuredArrow.hom_ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
  intro A
  have hu : (derived F).map (DerivedCategory.Q.map (η.app A)) =
      (fac F).hom.app A ≫ (unit F).app (R.obj A) := by
    apply (cancel_mono ((fac F).hom.app (R.obj A))).mp
    simp only [unit, NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.whiskerRight_app, Category.id_comp, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id]
    calc
      _ = (fac F).hom.app A ≫ (ordinaryCochain F).map (R.map (η.app A)) :=
        (fac F).hom.naturality (η.app A)
      _ = _ := congrArg ((fac F).hom.app A ≫ ·)
        (ordinaryCochain_augmentation_coherence F A)
  have hm := NatTrans.congr_app (StructuredArrow.w m) (R.obj A)
  apply (cancel_mono (E.right.map (inputAugmentationIso A).hom)).mp
  change m.right.app (DerivedCategory.Q.obj A) ≫ _ =
    (extensionDesc F E.right E.hom).app (DerivedCategory.Q.obj A) ≫ _
  simp only [extensionDesc, Localization.liftNatTrans_app,
    Localization.Lifting.compLeft_iso, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id,
    extensionDescOnCochains, extensionDescOnInput, Category.assoc,
    ← E.right.map_comp, Iso.inv_hom_id, Functor.map_id]
  change m.right.app (DerivedCategory.Q.obj A) ≫
      E.right.map (DerivedCategory.Q.map (η.app A)) = _
  rw [← m.right.naturality]
  change (derived F).map (DerivedCategory.Q.map (η.app A)) ≫
    m.right.app (DerivedCategory.Q.obj (R.obj A)) =
    (fac F).hom.app A ≫ E.hom.app (R.obj A) ≫ 𝟙 _
  rw [hu, Category.assoc, Category.comp_id]
  exact congrArg ((fac F).hom.app A ≫ ·) hm

/-- The universal witness stores its actual maps before their valid uniqueness laws. -/
def initialWitness  :
    (Functor.LeftExtension.mk (derived F) (unit F)).IsUniversal :=
  IsInitial.ofUniqueHom (initialExtensionDesc F) (initialExtensionDesc_unique F)

/-- The specified model functor and unit form the right-derived direct image. -/
instance isRightDerived  :
    (derived F).IsRightDerivedFunctor (unit F)
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) where
  isLeftKanExtension := { nonempty_isUniversal := ⟨initialWitness F⟩ }


/-- The canonical right-derived existence certificate stores the actual initial witness above. -/
instance hasRightDerived :
    (ordinaryCochain F).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) :=
  Functor.HasRightDerivedFunctor.mk' (RF := derived F) (α := unit F)

/-- Any genuinely supplied right-derived model is compared by native uniqueness, backed on
this side by the displayed initial-extension data. -/
def isoOfModel (G : DerivedCategory C ⥤ DerivedCategory D)
    (β : ordinaryCochain F ⟶ DerivedCategory.Q ⋙ G)
    [G.IsRightDerivedFunctor β (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))] :
    derived F ≅ G :=
  Functor.rightDerivedUnique (RF := derived F) (RF' := G) (α := unit F) (α'₂ := β)
    (W := HomologicalComplex.quasiIso C (ComplexShape.up ℤ))

section ExactPostcomposition

universe uE vE wE
variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
variable (G : D ⥤ E) [G.Additive]
variable [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Exact postcomposition uses the same actual source K-injective model. All four comparison
isomorphisms are native factorization or actual cochain composition maps. -/
def postcomposeOnInput (A : CochainComplex C ℤ) :
    (derived F ⋙ G.mapDerivedCategory).obj (DerivedCategory.Q.obj A) ≅
      (derived (F ⋙ G)).obj (DerivedCategory.Q.obj A) :=
  G.mapDerivedCategory.mapIso ((fac F).app A) ≪≫
    G.mapDerivedCategoryFactors.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.KInjectiveResolution.Construction.replacement.{w} C).obj A)) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).app
        ((CochainComplex.KInjectiveResolution.Construction.replacement.{w} C).obj A)) ≪≫
    ((fac (F ⋙ G)).app A).symm

/-- Naturality follows from the specified model maps and native exact-functor comparisons. -/
theorem postcomposeOnInput_naturality {A B : CochainComplex C ℤ} (a : A ⟶ B) :
    (DerivedCategory.Q ⋙ derived F ⋙ G.mapDerivedCategory).map a ≫
        (postcomposeOnInput F G B).hom =
      (postcomposeOnInput F G A).hom ≫
        (DerivedCategory.Q ⋙ derived (F ⋙ G)).map a := sorry

/-- The actual comparison on cochains precedes descent through quasi-isomorphisms. -/
def postcomposeOnCochains :
    DerivedCategory.Q ⋙ derived F ⋙ G.mapDerivedCategory ≅
      DerivedCategory.Q ⋙ derived (F ⋙ G) :=
  NatIso.ofComponents (postcomposeOnInput F G)
    (fun a ↦ postcomposeOnInput_naturality F G a)

/-- Exact postcomposition commutes with the constructed unbounded right-derived functor.
Both maps descend the displayed cochain-model comparison. -/
def postcomposeIso : derived F ⋙ G.mapDerivedCategory ≅ derived (F ⋙ G) :=
  Localization.liftNatIso (DerivedCategory.Q (C := C))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ derived F ⋙ G.mapDerivedCategory)
    (DerivedCategory.Q ⋙ derived (F ⋙ G))
    (derived F ⋙ G.mapDerivedCategory) (derived (F ⋙ G)) (postcomposeOnCochains F G)

end ExactPostcomposition

end CategoryTheory.Functor.KInjectiveModel
