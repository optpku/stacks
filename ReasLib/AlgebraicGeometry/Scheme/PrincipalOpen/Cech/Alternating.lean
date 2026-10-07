module

public import ReasLib.AlgebraicGeometry.Scheme.PrincipalOpen.Cech.Product
public import ReasLib.AlgebraicTopology.Cech.OrderedIndex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.OverGlobal
public import ReasLib.Topology.Presheaf.Cech.Coordinates

/-!
# Strict alternating principal-open Cech complexes

This module provides the strictly indexed alternating Cech complex of a module sheaf on an
affine scheme, together with its totalization and augmentation from sections on the covered open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape HomologicalComplex₂
  RingedSpace.Module.Derived.Sections TopologicalSpace
open scoped BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PrincipalOpenCech

variable {A : Type u} [CommRing A] {r : ℕ}

namespace Alternating

/-- The affine ringed space on which the principal-open alternating Cech complex is formed. -/
abbrev affineRingedSpace (A : Type u) [CommRing A] : RingedSpace.{u} :=
  (Spec (CommRingCat.of A)).toRingedSpace

/-- The intersection of the principal opens selected by a strictly increasing Cech tuple. -/
abbrev intersectionOpen (f : Fin r → A) {p : ℕ}
    (σ : OrderedCechIndex (Fin r) p) :
    TopologicalSpace.Opens (affineRingedSpace A).carrier :=
  TopCat.Presheaf.Cech.intersection (fun i ↦ PrimeSpectrum.basicOpen (f i)) σ

/-- Sections on one strictly indexed principal-open intersection, regarded as modules over
`Γ(Spec(A), 𝒪)`. -/
abbrev sectionModule (f : Fin r → A) (F : (affineRingedSpace A).Modules)
    {p : ℕ} (σ : OrderedCechIndex (Fin r) p) :
    ModuleCat (RingedSpace.globalSectionsRing (affineRingedSpace A)) :=
  (OverGlobal.functor (affineRingedSpace A) (intersectionOpen f σ)).obj F

/-- Deleting an entry from a strict tuple enlarges its principal-open intersection. -/
theorem intersectionOpen_le_delete (f : Fin r → A) {p : ℕ}
    (σ : OrderedCechIndex (Fin r) (p + 1)) (j : Fin (p + 2)) :
    intersectionOpen f σ ≤ intersectionOpen f (σ.delete j) := sorry

/-- Restriction of sections from a deleted strict tuple to the full tuple. -/
noncomputable def restriction (f : Fin r → A) (F : (affineRingedSpace A).Modules)
    {p : ℕ} (σ : OrderedCechIndex (Fin r) (p + 1)) (j : Fin (p + 2)) :
    sectionModule f F (σ.delete j) ⟶ sectionModule f F σ :=
  (OverGlobal.restrictionOfLE (intersectionOpen_le_delete f σ j)).app F

/-- Degree `p` of the strict principal-open alternating Cech complex. -/
abbrev term (f : Fin r → A) (F : (affineRingedSpace A).Modules) (p : ℕ) :
    ModuleCat (RingedSpace.globalSectionsRing (affineRingedSpace A)) :=
  ∏ᶜ fun σ : OrderedCechIndex (Fin r) p ↦ sectionModule f F σ

/-- The `j`th coface on strictly indexed principal-open Cech terms. -/
noncomputable def coface (f : Fin r → A) (F : (affineRingedSpace A).Modules)
    (p : ℕ) (j : Fin (p + 2)) : term f F p ⟶ term f F (p + 1) :=
  Limits.Pi.map' (fun σ : OrderedCechIndex (Fin r) (p + 1) ↦ σ.delete j)
    (fun σ ↦ restriction f F σ j)

/-- The alternating restriction differential on strictly indexed principal-open Cech terms. -/
noncomputable def differential (f : Fin r → A) (F : (affineRingedSpace A).Modules)
    (p : ℕ) : term f F p ⟶ term f F (p + 1) :=
  ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • coface f F p j

/-- Consecutive strict principal-open alternating Cech differentials compose to zero. -/
theorem differential_comp (f : Fin r → A) (F : (affineRingedSpace A).Modules)
    (p : ℕ) : differential f F p ≫ differential f F (p + 1) = 0 := sorry

/-- The principal-open alternating Cech complex indexed by strictly increasing tuples. -/
noncomputable def complex (f : Fin r → A) (F : (affineRingedSpace A).Modules) :
    CochainComplex (ModuleCat (RingedSpace.globalSectionsRing (affineRingedSpace A))) ℕ :=
  CochainComplex.of (term f F) (differential f F) (differential_comp f F)

/-- A map of module sheaves acts coordinatewise on strict alternating Cech terms. -/
noncomputable def termMap (f : Fin r → A) {F G : (affineRingedSpace A).Modules}
    (g : F ⟶ G) (p : ℕ) : term f F p ⟶ term f G p :=
  Limits.Pi.map fun σ ↦
    (OverGlobal.functor (affineRingedSpace A) (intersectionOpen f σ)).map g

/-- Coordinatewise maps of module sections commute with the strict Cech differential. -/
theorem termMap_comm (f : Fin r → A) {F G : (affineRingedSpace A).Modules}
    (g : F ⟶ G) {p q : ℕ} :
    termMap f g p ≫ (complex f G).d p q =
      (complex f F).d p q ≫ termMap f g q := sorry

/-- The map of strict principal-open alternating Cech complexes induced by a module-sheaf map. -/
noncomputable def complexMap (f : Fin r → A) {F G : (affineRingedSpace A).Modules}
    (g : F ⟶ G) : complex f F ⟶ complex f G where
  f p := termMap f g p
  comm' := fun _ _ _ ↦ termMap_comm f g

/-- The strict alternating Cech-complex map induced by an identity is the identity. -/
theorem complexMap_id (f : Fin r → A) (F : (affineRingedSpace A).Modules) :
    complexMap f (𝟙 F) = 𝟙 (complex f F) := sorry

/-- Strict alternating Cech-complex maps respect composition. -/
theorem complexMap_comp (f : Fin r → A) {F G H : (affineRingedSpace A).Modules}
    (g : F ⟶ G) (h : G ⟶ H) :
    complexMap f (g ≫ h) = complexMap f g ≫ complexMap f h := sorry

/-- The strictly indexed principal-open alternating Cech complex, functorial in its module
sheaf. -/
noncomputable def complexFunctor (f : Fin r → A) :
    (affineRingedSpace A).Modules ⥤
      CochainComplex (ModuleCat (RingedSpace.globalSectionsRing (affineRingedSpace A))) ℕ where
  obj F := complex f F
  map g := complexMap f g
  map_id F := complexMap_id f F
  map_comp g h := complexMap_comp f g h

/-- The strict alternating principal-open Cech functor preserves zero morphisms. -/
instance complexFunctor_preservesZeroMorphisms (f : Fin r → A) :
    (complexFunctor f).PreservesZeroMorphisms := sorry

/-- The strict alternating Cech-row functor extended from `ℕ` to `ℤ`. -/
abbrev row (f : Fin r → A) :
    (affineRingedSpace A).Modules ⥤
      CochainComplex (ModuleCat (RingedSpace.globalSectionsRing (affineRingedSpace A))) ℤ :=
  complexFunctor f ⋙ embeddingUpNat.extendFunctor _

/-- The total strict alternating Cech functor on unbounded complexes of module sheaves. -/
abbrev total (f : Fin r → A) :
    CochainComplex (affineRingedSpace A).Modules ℤ ⥤
      CochainComplex (ModuleCat (RingedSpace.globalSectionsRing (affineRingedSpace A))) ℤ :=
  (row f).mapHomologicalComplex (up ℤ) ⋙
    totalFunctor _ (up ℤ) (up ℤ) (up ℤ)

/-- Sections on the union of the principal opens, viewed over the affine global-section ring. -/
abbrev sectionsOnUnion (f : Fin r → A) :
    (affineRingedSpace A).Modules ⥤
      ModuleCat (RingedSpace.globalSectionsRing (affineRingedSpace A)) :=
  OverGlobal.functor (affineRingedSpace A) (openSubset f)

/-- Every strict principal-open intersection lies in the union of the principal opens. -/
theorem intersectionOpen_le_openSubset (f : Fin r → A)
    (σ : OrderedCechIndex (Fin r) 0) : intersectionOpen f σ ≤ openSubset f := sorry

/-- Restriction from the principal-open union to the degree-zero strict Cech term. -/
noncomputable def augmentationMap (f : Fin r → A) (F : (affineRingedSpace A).Modules) :
    (sectionsOnUnion f).obj F ⟶ term f F 0 :=
  Limits.Pi.lift fun σ ↦
    (OverGlobal.restrictionOfLE (intersectionOpen_le_openSubset f σ)).app F

/-- The degree-zero restriction map is natural in the module sheaf. -/
theorem augmentationMap_naturality (f : Fin r → A)
    {F G : (affineRingedSpace A).Modules} (g : F ⟶ G) :
    (sectionsOnUnion f).map g ≫ augmentationMap f G =
      augmentationMap f F ≫ termMap f g 0 := sorry

/-- The degree-zero row of the strict alternating Cech bicomplex of a sheaf complex. -/
abbrev zeroRow (f : Fin r → A)
    (K : CochainComplex (affineRingedSpace A).Modules ℤ) :
    CochainComplex (ModuleCat (RingedSpace.globalSectionsRing (affineRingedSpace A))) ℤ :=
  ((HomologicalComplex.eval _ (up ℤ) 0).mapHomologicalComplex (up ℤ)).obj
    (((row f).mapHomologicalComplex (up ℤ)).obj K)

/-- The degreewise restriction into the zero row of the strict alternating Cech bicomplex. -/
noncomputable def augmentationZeroRowComponent (f : Fin r → A)
    (K : CochainComplex (affineRingedSpace A).Modules ℤ) (n : ℤ) :
    (((sectionsOnUnion f).mapHomologicalComplex (up ℤ)).obj K).X n ⟶
      (zeroRow f K).X n :=
  augmentationMap f (K.X n) ≫
    ((complex f (K.X n)).extendXIso embeddingUpNat embeddingUpNat_zero).inv

/-- The degreewise union-to-Cech restrictions commute with the differential of the sheaf
complex. -/
theorem augmentationZeroRowComponent_comm (f : Fin r → A)
    (K : CochainComplex (affineRingedSpace A).Modules ℤ) {n n' : ℤ}
    (hnn' : (up ℤ).Rel n n') :
    augmentationZeroRowComponent f K n ≫ (zeroRow f K).d n n' =
      (((sectionsOnUnion f).mapHomologicalComplex (up ℤ)).obj K).d n n' ≫
        augmentationZeroRowComponent f K n' := sorry

/-- The section restrictions assemble into the zero row of the strict alternating Cech
bicomplex. -/
noncomputable def augmentationZeroRow (f : Fin r → A)
    (K : CochainComplex (affineRingedSpace A).Modules ℤ) :
    ((sectionsOnUnion f).mapHomologicalComplex (up ℤ)).obj K ⟶ zeroRow f K where
  f n := augmentationZeroRowComponent f K n
  comm' := fun _ _ h ↦ augmentationZeroRowComponent_comm f K h

/-- The degree-zero strict Cech augmentation lands in vertical cycles. -/
theorem augmentationZeroRow_cycles (f : Fin r → A)
    (K : CochainComplex (affineRingedSpace A).Modules ℤ) :
    ∀ n : ℤ, (augmentationZeroRow f K).f n ≫
      ((((row f).mapHomologicalComplex (up ℤ)).obj K).X n).d 0 1 = 0 := sorry

/-- The canonical augmentation from sections on the principal-open union to the total strict
alternating Cech complex. -/
noncomputable def augmentation (f : Fin r → A)
    (K : CochainComplex (affineRingedSpace A).Modules ℤ) :
    ((sectionsOnUnion f).mapHomologicalComplex (up ℤ)).obj K ⟶ (total f).obj K :=
  ZeroRow.ToTotal.map (augmentationZeroRow f K) (augmentationZeroRow_cycles f K)

/-- The total strict alternating Cech augmentation is natural in the sheaf complex. -/
theorem augmentation_naturality (f : Fin r → A)
    {K L : CochainComplex (affineRingedSpace A).Modules ℤ} (g : K ⟶ L) :
    ((sectionsOnUnion f).mapHomologicalComplex (up ℤ)).map g ≫ augmentation f L =
      augmentation f K ≫ (total f).map g := sorry

/-- The functorial augmentation from union sections to the total strict alternating Cech
complex. -/
noncomputable def augmentationNatTrans (f : Fin r → A) :
    (sectionsOnUnion f).mapHomologicalComplex (up ℤ) ⟶ total f where
  app K := augmentation f K
  naturality := fun _ _ g ↦ augmentation_naturality f g

/-- The total strict alternating principal-open Cech complex in `D(A)`. -/
abbrev source (f : Fin r → A) :
    CochainComplex (affineRingedSpace A).Modules ℤ ⥤
      DerivedCategory (ModuleCat.{u, u} A) :=
  total f ⋙ DerivedCategory.Q ⋙
    ModuleCat.derivedRestrictionOfScalars (ΓSpecIso (CommRingCat.of A)).inv.hom

end Alternating

end AlgebraicGeometry.Scheme.PrincipalOpenCech
