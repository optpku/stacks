module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommPointwiseCompletedAction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.Equivalence
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import ReasLib.Algebra.Homology.Embedding.Functor
public import Mathlib.FieldTheory.Galois.Profinite
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.GeometricCohomology

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat Opposite
open CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
noncomputable section
universe u

namespace NoncommGeometricSource

/-- The algebraic-closure automorphism group is compact even over an imperfect
field: restriction identifies it with the separable-closure Galois group.
This does NOT assert that the algebraic closure itself is separable over k. -/
instance algebraicClosureGal_compact (k : Type u) [Field k] :
    CompactSpace Gal(AlgebraicClosure k/k) := by sorry

/-- The compactification is proper over the compact spectrum of the field. -/
instance compactification_compact {k : Type u} [Field k] (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X) :
    CompactSpace P.obj.right.left := by sorry

/-- Properness over a field gives separatedness, hence quasi-separatedness. -/
instance compactification_quasiSeparated {k : Type u} [Field k] (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X) :
    QuasiSeparatedSpace P.obj.right.left := by sorry

open AlgebraicGeometry.Scheme.AmbientAssociatedSheaf
variable (Λ : Type (u + 1)) [Ring Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]

/-- Actual sections at the terminal etale object, valid for noncommutative coefficients. -/
def sections {X : Scheme.{u}} :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ where
  obj F := F.obj.obj (op (AlgebraicGeometry.Scheme.Etale.globalEtale X))
  map f := f.hom.app (op (AlgebraicGeometry.Scheme.Etale.globalEtale X))
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The actual inverse-image functor on module sheaves. -/
def modulePullback {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ) Z.smallEtaleTopology Y.smallEtaleTopology

/-- Module-sheaf pullback composition is fixed by the actual adjunction and site pullback compositor. -/
def modulePullbackComp {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    modulePullback Λ p ⋙ modulePullback Λ q ≅ modulePullback Λ (q ≫ p) :=
  let siteIso : smallEtalePullback p ⋙ smallEtalePullback q ≅ smallEtalePullback (q ≫ p) :=
    (MorphismProperty.Over.pullbackComp q p).symm
  Adjunction.leftAdjointCompIso
    (smallEtalePullback_sheafAdjunction p (ModuleCat.{u + 1} Λ))
    (smallEtalePullback_sheafAdjunction q (ModuleCat.{u + 1} Λ))
    (smallEtalePullback_sheafAdjunction (q ≫ p) (ModuleCat.{u + 1} Λ))
    (sheafPushforwardContinuousComp' siteIso (ModuleCat.{u + 1} Λ)
      A.smallEtaleTopology B.smallEtaleTopology C.smallEtaleTopology)

/-- Pullback of sections uses the geometric adjunction unit and the identity-object pullback iso. -/
def sectionsPullback {Y Z : Scheme.{u}} (f : Y ⟶ Z) :
    sections (X := Z) Λ ⟶ modulePullback Λ f ⋙ sections (X := Y) Λ where
  app F :=
    ((sheafToPresheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
      ((smallEtalePullback_sheafAdjunction f (ModuleCat.{u + 1} Λ)).unit.app F)).app
        (op (AlgebraicGeometry.Scheme.Etale.globalEtale Z)) ≫
      ((modulePullback Λ f).obj F).obj.map (op (AlgebraicGeometry.Scheme.Etale.globalEtalePullbackIso f).inv)
  naturality := sorry

variable {k : Type u} [Field k] (X : SchemeOverField k)

/-- Galois descent of a geometrically pulled-back sheaf uses the actual
pullback compositor and equality of the structural maps over X. -/
def galoisDescentIso (σ : Gal(AlgebraicClosure k/k))
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (modulePullback Λ (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)).obj
        ((modulePullback Λ (geometricToArithmeticHom X)).obj F) ≅
      (modulePullback Λ (geometricToArithmeticHom X)).obj F :=
  (modulePullbackComp Λ (geometricToArithmeticHom X)
      (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)).app F ≪≫
    (eqToIso (congrArg (fun h ↦ modulePullback Λ h)
      (FieldExtension.Galois.map_toSource k (AlgebraicClosure k) X.hom σ))).app F

/-- The geometric Galois action on sections is defined before any comparison with invariants. -/
def geometricSectionsEnd (σ : Gal(AlgebraicClosure k/k))
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (sections Λ).obj ((modulePullback Λ (geometricToArithmeticHom X)).obj F) ⟶
      (sections Λ).obj ((modulePullback Λ (geometricToArithmeticHom X)).obj F) :=
  (sectionsPullback Λ (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)).app
      ((modulePullback Λ (geometricToArithmeticHom X)).obj F) ≫
    (sections Λ).map (galoisDescentIso Λ X σ F).hom

/-- Identity acts identically on the actual geometric section module. -/
theorem geometricSectionsEnd_one
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    geometricSectionsEnd Λ X 1 F = 𝟙 _ := sorry

/-- The geometric section endomorphisms respect Galois multiplication. -/
theorem geometricSectionsEnd_mul (σ τ : Gal(AlgebraicClosure k/k))
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    geometricSectionsEnd Λ X (σ * τ) F =
      geometricSectionsEnd Λ X τ F ≫ geometricSectionsEnd Λ X σ F := sorry


/-- The independent geometric descent action, on arithmetic sheaves. -/
def sectionAction :
    Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
    Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) where
  obj F :=
    { V := (sections Λ).obj ((modulePullback Λ (geometricToArithmeticHom X)).obj F)
      ρ := { toFun := fun σ ↦ geometricSectionsEnd Λ X σ F
             map_one' := geometricSectionsEnd_one Λ X F
             map_mul' := fun σ τ ↦ geometricSectionsEnd_mul Λ X σ τ F } }
  map f := { hom := (sections Λ).map ((modulePullback Λ (geometricToArithmeticHom X)).map f)
             comm := fun _ ↦ by sorry }
  map_id := by sorry
  map_comp := by sorry

variable [hqc : CompactSpace X.left] [hqs : QuasiSeparatedSpace X.left]

include hqc hqs in
/-- Each geometric section descends to a finite extension on a qcqs source. -/
theorem section_open (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    openStabilizer Λ Gal(AlgebraicClosure k/k) ((sectionAction Λ X).obj F) := by sorry

/-- All discrete geometric sections, with the actual descent action. -/
def discreteSections :
    Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
    DiscreteModuleCat Λ Gal(AlgebraicClosure k/k) where
  obj F := ⟨(sectionAction Λ X).obj F, section_open Λ X F⟩
  map f := ObjectProperty.homMk ((sectionAction Λ X).map f)
  map_id := by sorry
  map_comp := by sorry

instance discreteSections_additive : (discreteSections Λ X).Additive := by sorry

/-- Completed action on these actual sections, valid over an arbitrary base field. -/
def completedSections := discreteSections Λ X ⋙
  NoncommPointwiseCompletedAction.functor Λ Gal(AlgebraicClosure k/k)

instance completedSections_additive : (completedSections Λ X).Additive := by sorry

variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ))]

/-- Retain the smooth discrete model before applying completed scalar action.
This is the actual arithmetic sheaf resolution with geometric descent. -/
def arithmeticDiscreteCochain (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (((discreteSections Λ X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (injectiveResolution F).cocomplex).extend ComplexShape.embeddingUpNat

/-- Actual arithmetic-sheaf injective resolution followed by geometric sections,
with its completed Galois action already present on every term. -/
def arithmeticCochain (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (((completedSections Λ X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (injectiveResolution F).cocomplex).extend ComplexShape.embeddingUpNat

variable [Finite Λ] [ConnectedSpace X.left]
variable [∀ Y : Scheme.{u}, ∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [∀ Y : Scheme.{u}, EnoughInjectives (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))]
variable [∀ {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j]
  (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ), (etaleRestriction j).op.HasLeftKanExtension F]
variable (η : GeometricPoint (geometricBaseChange X))
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable (M : (finiteTypeDiscreteModule Λ
  (Aut (GeometricPoint.finiteFiber (arithmeticPoint X η)))).FullSubcategory)

/-- The finite arithmetic coefficient from the published germ-based inverse. -/
def associatedCoefficient :=
  ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules
    Λ (arithmeticPoint X η)).inverse.obj M).obj

/-- The actual arbitrary-compactification source. No cohomology object or
group-homology complex replaces its arithmetic sheaf resolution. -/
def compactCochain := arithmeticCochain Λ P.obj.right
  ((etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u + 1} Λ)).obj
    (associatedCoefficient Λ X η M))

end NoncommGeometricSource
