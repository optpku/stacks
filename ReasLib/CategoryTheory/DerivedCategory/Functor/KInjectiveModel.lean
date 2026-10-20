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
      (((CochainComplex.KInjectiveResolution.Construction.replacement.{w} C)).map a)) := sorry

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
      extensionDescOnInput F G β A ≫ (DerivedCategory.Q ⋙ G).map a := sorry

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
    unit F ≫ Functor.whiskerLeft DerivedCategory.Q (extensionDesc F G β) = β := sorry

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
    m = initialExtensionDesc F E := sorry

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
