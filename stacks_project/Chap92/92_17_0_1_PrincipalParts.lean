/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.Single
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import ReasLib.Algebra.Module.PrincipalParts.RingHom.BaseChange
public import ReasLib.Algebra.Module.PrincipalParts.RingHom.FirstOrder
public import stacks_project.Chap110.Lemma_110_43_1_Cotangent
public import stacks_project.Chap92.Lemma_92_4_1_PolynomialOver

/-!
# First principal parts of a module on the polynomial site

For an `A`-algebra `B` and a `B`-module `M`, this module owns the simplicial `P_•`-module
`P¹_{P_n/A}(restrictScalars (augmentationHom n) M)`, the first principal-parts sequence of
those `P_n`-modules, the underived degreewise extension-of-scalars functor along
`P_n → B` (to be left-derived), and the Lemma 92.4.1 evaluation complexes of the flat
cotangent tensor and of the constant module `M`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal
open Opposite
open AlgebraicTopology
open HomologicalComplex
open ComplexShape
open scoped Simplicial

noncomputable section

universe u

namespace Algebra.CotangentComplex.Atiyah

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
include A B

/-- The object of `Under (CommRingCat.of A)` associated to an `A`-algebra `B`. -/
abbrev under : Under (CommRingCat.of A) :=
  Under.mk (CommRingCat.ofHom (algebraMap A B))

/-- The degree-`n` standard polynomial resolution term of `B` over `A`. -/
abbrev standardTerm (n : SimplexCategoryᵒᵖ) : Under (CommRingCat.of A) :=
  CommRingCat.Under.CotangentComplex.standardTerm (CommRingCat.of A) (under A B) n

/-- The structure map `A →+* P_n` of a standard-resolution term. -/
abbrev structureHom (n : SimplexCategoryᵒᵖ) : A →+* (standardTerm A B n).right :=
  (standardTerm A B n).hom.hom

/-- The augmentation `P_n →+* B` of a standard-resolution term. -/
abbrev augmentationHom (n : SimplexCategoryᵒᵖ) : (standardTerm A B n).right →+* B :=
  (CommRingCat.Under.CotangentComplex.standardAugmentation
    (CommRingCat.of A) (under A B) n).hom

/-- The ring map of standard-resolution terms induced by a simplex operator. -/
@[irreducible] def termMapHom {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (standardTerm A B n).right →+* (standardTerm A B m).right :=
  (CommRingCat.Under.CotangentComplex.standardMap (CommRingCat.of A) (under A B) φ).right.hom

/-- Restriction of a `B`-module along the standard-resolution augmentation `P_n → B`. -/
abbrev restrictModule (M : ModuleCat.{u} B) (n : SimplexCategoryᵒᵖ) :
    ModuleCat.{u} (standardTerm A B n).right :=
  (ModuleCat.restrictScalars (augmentationHom A B n)).obj M

/-- The structure maps `A → P_n → P_m` and `A → P_m` agree. -/
theorem termMapHom_comp_structureHom {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (termMapHom A B φ).comp (structureHom A B n) = structureHom A B m :=
  sorry

/-- The augmentations `P_n → B` and `P_n → P_m → B` agree. -/
theorem termMapHom_comp_augmentationHom {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    augmentationHom A B n = (augmentationHom A B m).comp (termMapHom A B φ) :=
  sorry

/-- Identity on the source ring, used to present a ring-map square to the principal-parts
base-change adapter. -/
theorem square_comp_id {P Q : Type u} [CommRing P] [CommRing Q]
    (σ : A →+* P) (σ' : A →+* Q) (b : P →+* Q) (hσ : b.comp σ = σ') :
    b.comp σ = σ'.comp (RingHom.id A) :=
  sorry

/-- Restriction of `M` along `P → Q → B` compared with restriction along `P → B`. -/
def restrictModuleComp {P Q : Type u} [CommRing P] [CommRing Q]
    (b : P →+* Q) (τ : P →+* (under A B).right) (τ' : Q →+* (under A B).right)
    (hτ : τ = τ'.comp b) (M : ModuleCat.{u} (under A B).right) :
    (ModuleCat.restrictScalars τ).obj M ⟶
      (ModuleCat.restrictScalars b).obj ((ModuleCat.restrictScalars τ').obj M) :=
  (ModuleCat.restrictScalarsComp' b τ' τ hτ).hom.app M

/-- The genuine first principal-parts sequence of `P`-modules associated to `P → B`. -/
def moduleSequence {P : Type u} [CommRing P] (σ : A →+* P) (τ : P →+* B)
    (M : ModuleCat.{u} B) : ShortComplex (ModuleCat.{u} P) :=
  PrincipalParts.RingHom.FirstOrder.sequence σ ((ModuleCat.restrictScalars τ).obj M)

/-- Unfolding of `moduleSequence` as the canonical first-order sequence of the restricted
module. -/
theorem moduleSequence_eq {P : Type u} [CommRing P] (σ : A →+* P) (τ : P →+* B)
    (M : ModuleCat.{u} B) :
    moduleSequence A B σ τ M =
      PrincipalParts.RingHom.FirstOrder.sequence σ
        ((ModuleCat.restrictScalars τ).obj M) :=
  sorry

/-- The first principal-parts sequence of `P`-modules is short exact. -/
theorem moduleSequence_shortExact {P : Type u} [CommRing P] (σ : A →+* P)
    (τ : P →+* B) (M : ModuleCat.{u} B) :
    (moduleSequence A B σ τ M).ShortExact :=
  PrincipalParts.RingHom.FirstOrder.shortExact σ ((ModuleCat.restrictScalars τ).obj M)

/-- The standard polynomial resolution as a simplicial commutative ring. -/
def standardSimplicialCommRing : SimplexCategoryᵒᵖ ⥤ CommRingCat.{u} where
  obj n := (standardTerm A B n).right
  map φ :=
    (CommRingCat.Under.CotangentComplex.standardMap (CommRingCat.of A) (under A B) φ).right
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The standard polynomial resolution as a simplicial ring. -/
def standardSimplicialRing : SimplexCategoryᵒᵖ ⥤ RingCat.{u} where
  obj n := RingCat.of (standardTerm A B n).right
  map φ := RingCat.ofHom (termMapHom A B φ)
  map_id _ := sorry
  map_comp _ _ := sorry

/-- Unfolding of `standardSimplicialRing` on objects as the underlying ring of a standard term. -/
theorem standardSimplicialRing_obj (n : SimplexCategoryᵒᵖ) :
    (standardSimplicialRing A B).obj n = RingCat.of (standardTerm A B n).right :=
  sorry

/-- The underlying type of a standard simplicial ring object is a commutative ring. -/
instance standardSimplicialRing_commRing (n : SimplexCategoryᵒᵖ) :
    CommRing ((standardSimplicialRing A B).obj n : Type u) :=
  inferInstanceAs (CommRing (standardTerm A B n).right)

/-- The constant simplicial commutative ring on `B`. -/
def constantSimplicialCommRing : SimplexCategoryᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const _).obj (under A B).right

/-- The constant simplicial ring on `B`. -/
def constantSimplicialRing : SimplexCategoryᵒᵖ ⥤ RingCat.{u} where
  obj _ := RingCat.of (under A B).right
  map _ := RingCat.ofHom (RingHom.id B)
  map_id _ := sorry
  map_comp _ _ := sorry

/-- Unfolding of `constantSimplicialRing` on objects as the underlying ring of `B`. -/
theorem constantSimplicialRing_obj (n : SimplexCategoryᵒᵖ) :
    (constantSimplicialRing A B).obj n = RingCat.of (under A B).right :=
  sorry

/-- The augmentation `P_• ⟶ B` as a map of simplicial commutative rings. -/
def augmentationCommRing :
    standardSimplicialCommRing A B ⟶ constantSimplicialCommRing A B where
  app n :=
    CommRingCat.Under.CotangentComplex.standardAugmentation
      (CommRingCat.of A) (under A B) n
  naturality _ _ _ := sorry

/-- The augmentation `P_• ⟶ B` as a map of simplicial rings. -/
def augmentation : standardSimplicialRing A B ⟶ constantSimplicialRing A B where
  app n := RingCat.ofHom (augmentationHom A B n)
  naturality _ _ _ := sorry

/-- A component of `augmentation` is the standard-resolution augmentation in that degree. -/
theorem augmentation_app (n : SimplexCategoryᵒᵖ) :
    (augmentation A B).app n = RingCat.ofHom (augmentationHom A B n) :=
  sorry

/-- The simplicial `P_•`-module obtained by restricting `M` along `P_n → B`. -/
def restrictedModule (M : ModuleCat.{u} B) :
    PresheafOfModules.{u} (standardSimplicialRing A B) where
  obj n := restrictModule A B M n
  map {n m} φ :=
    restrictModuleComp A B (termMapHom A B φ) (augmentationHom A B n)
      (augmentationHom A B m) (termMapHom_comp_augmentationHom A B φ) M
  map_id _ := sorry
  map_comp _ _ := sorry

/-- Degreewise, `restrictedModule` is restriction of scalars of `M` along the augmentation. -/
theorem restrictedModule_obj (M : ModuleCat.{u} B) (n : SimplexCategoryᵒᵖ) :
    (restrictedModule A B M).obj n = restrictModule A B M n :=
  sorry

/-- A simplicial operator of the standard resolution commutes with the structure maps. -/
theorem termMapHom_comp_structureHom_under {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (standardTerm A B n).hom ≫ CommRingCat.ofHom (termMapHom A B φ) =
      (standardTerm A B m).hom :=
  sorry

/-- The Kähler comparison of standard-resolution terms, as a map of differentials. -/
def standardDifferentialsMap {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    CommRingCat.KaehlerDifferential (standardTerm A B n).hom ⟶
      (ModuleCat.restrictScalars (termMapHom A B φ)).obj
        (CommRingCat.KaehlerDifferential (standardTerm A B m).hom) :=
  CommRingCat.KaehlerDifferential.map
    ((Category.id_comp (standardTerm A B m).hom).trans
      (termMapHom_comp_structureHom_under A B φ).symm)

/-- The comparison from a `P`-tensor of restrictions to the restriction of a `Q`-tensor. -/
def restrictCotangentTensor {P Q : Type u} [CommRing P] [CommRing Q]
    (b : P →+* Q) (f : CommRingCat.of A ⟶ CommRingCat.of Q) (N : ModuleCat.{u} Q) :
    (ModuleCat.restrictScalars b).obj (CommRingCat.KaehlerDifferential f) ⊗
        (ModuleCat.restrictScalars b).obj N ⟶
      (ModuleCat.restrictScalars b).obj (CommRingCat.KaehlerDifferential f ⊗ N) :=
  μ (ModuleCat.restrictScalars b) (CommRingCat.KaehlerDifferential f) N

/-- Restriction of first-order cotangent tensors along a simplex operator. -/
def cotangentRestrictHom (M : ModuleCat.{u} B) {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    PrincipalParts.RingHom.FirstOrder.cotangent (structureHom A B n)
        (restrictModule A B M n) ⟶
      (ModuleCat.restrictScalars ((standardSimplicialRing A B).map φ).hom).obj
        (PrincipalParts.RingHom.FirstOrder.cotangent (structureHom A B m)
          (restrictModule A B M m)) :=
  tensorHom (standardDifferentialsMap A B φ)
      (restrictModuleComp A B (termMapHom A B φ) (augmentationHom A B n)
        (augmentationHom A B m) (termMapHom_comp_augmentationHom A B φ) M) ≫
    μ (ModuleCat.restrictScalars (termMapHom A B φ))
      (CommRingCat.KaehlerDifferential (standardTerm A B m).hom)
      (restrictModule A B M m)

/-- The simplicial `P_•`-module `Ω_{P_n/A} ⊗_{P_n} M`. -/
def cotangentModule (M : ModuleCat.{u} B) :
    PresheafOfModules.{u} (standardSimplicialRing A B) where
  obj n :=
    PrincipalParts.RingHom.FirstOrder.cotangent (structureHom A B n)
      (restrictModule A B M n)
  map φ := cotangentRestrictHom A B M φ
  map_id _ := sorry
  map_comp _ _ := sorry

/-- Degreewise, `cotangentModule` is the Kähler tensor of the restricted module. -/
theorem cotangentModule_obj (M : ModuleCat.{u} B) (n : SimplexCategoryᵒᵖ) :
    (cotangentModule A B M).obj n =
      PrincipalParts.RingHom.FirstOrder.cotangent (structureHom A B n)
        (restrictModule A B M n) :=
  sorry

/-- Base change of first principal parts along an explicit commuting square. -/
def principalPartsRestrictMap {P Q : Type u} [CommRing P] [CommRing Q]
    (σ : A →+* P) (σ' : A →+* Q) (τ : P →+* B) (τ' : Q →+* B) (b : P →+* Q)
    (hσ : b.comp σ = σ') (hτ : τ = τ'.comp b) (M : ModuleCat.{u} B) :
    PrincipalParts.RingHom.module σ ((ModuleCat.restrictScalars τ).obj M) 1 ⟶
      (ModuleCat.restrictScalars b).obj
        (PrincipalParts.RingHom.module σ' ((ModuleCat.restrictScalars τ').obj M) 1) :=
  PrincipalParts.RingHom.BaseChange.map σ σ' (RingHom.id A) b
    (square_comp_id A B σ σ' b hσ) 1 (restrictModuleComp A B b τ τ' hτ M)

/-- The simplicial `P_•`-module `P¹_{P_n/A}(restrictScalars (augmentationHom n) M)`. -/
def principalPartsModule (M : ModuleCat.{u} B) :
    PresheafOfModules.{u} (standardSimplicialRing A B) where
  obj n :=
    PrincipalParts.RingHom.module (structureHom A B n) (restrictModule A B M n) 1
  map {n m} φ :=
    principalPartsRestrictMap A B (structureHom A B n) (structureHom A B m)
      (augmentationHom A B n) (augmentationHom A B m) (termMapHom A B φ)
      (termMapHom_comp_structureHom A B φ) (termMapHom_comp_augmentationHom A B φ) M
  map_id _ := sorry
  map_comp _ _ := sorry

/-- Degreewise, `principalPartsModule` is first principal parts of the restricted module. -/
theorem principalPartsModule_obj (M : ModuleCat.{u} B) (n : SimplexCategoryᵒᵖ) :
    (principalPartsModule A B M).obj n =
      PrincipalParts.RingHom.module (structureHom A B n) (restrictModule A B M n) 1 :=
  sorry

/-- The first-order cotangent arrow in degree `n`, as a map of `P_n`-modules. -/
def cotangentToDegree (M : ModuleCat.{u} B) (n : SimplexCategoryᵒᵖ) :
    (cotangentModule A B M).obj n ⟶ (principalPartsModule A B M).obj n :=
  PrincipalParts.RingHom.FirstOrder.cotangentTo (structureHom A B n)
    (restrictModule A B M n)

/-- The first-order projection in degree `n`, as a map of `P_n`-modules. -/
def projectionDegree (M : ModuleCat.{u} B) (n : SimplexCategoryᵒᵖ) :
    (principalPartsModule A B M).obj n ⟶ (restrictedModule A B M).obj n :=
  PrincipalParts.RingHom.FirstOrder.projection (structureHom A B n)
    (restrictModule A B M n)

/-- The assembled cotangent arrow of the simplicial first principal-parts sequence. -/
def principalPartsSequence_f (M : ModuleCat.{u} B) :
    cotangentModule A B M ⟶ principalPartsModule A B M where
  app n := cotangentToDegree A B M n
  naturality := fun {X Y} f => sorry

/-- The assembled projection of the simplicial first principal-parts sequence. -/
def principalPartsSequence_g (M : ModuleCat.{u} B) :
    principalPartsModule A B M ⟶ restrictedModule A B M where
  app n := projectionDegree A B M n
  naturality := fun {X Y} f => sorry

/-- The two assembled principal-parts arrows compose to zero. -/
theorem principalPartsSequence_zero (M : ModuleCat.{u} B) :
    principalPartsSequence_f A B M ≫ principalPartsSequence_g A B M = 0 :=
  sorry

/-- The short complex of simplicial `P_•`-modules
`Ω_{P_•/A} ⊗ M ⟶ P¹_{P_•/A}(M) ⟶ M`. -/
def principalPartsSequence (M : ModuleCat.{u} B) :
    ShortComplex (PresheafOfModules.{u} (standardSimplicialRing A B)) :=
  ShortComplex.mk (principalPartsSequence_f A B M) (principalPartsSequence_g A B M)
    (principalPartsSequence_zero A B M)

/-- Unfolding of `principalPartsSequence` as a short complex with the assembled arrows. -/
theorem principalPartsSequence_eq (M : ModuleCat.{u} B) :
    principalPartsSequence A B M =
      ShortComplex.mk (principalPartsSequence_f A B M) (principalPartsSequence_g A B M)
        (principalPartsSequence_zero A B M) :=
  sorry

/-- The left term of `principalPartsSequence` is the assembled cotangent module. -/
theorem principalPartsSequence_X₁ (M : ModuleCat.{u} B) :
    (principalPartsSequence A B M).X₁ = cotangentModule A B M :=
  sorry

/-- The middle term of `principalPartsSequence` is the assembled first principal-parts module. -/
theorem principalPartsSequence_X₂ (M : ModuleCat.{u} B) :
    (principalPartsSequence A B M).X₂ = principalPartsModule A B M :=
  sorry

/-- The right term of `principalPartsSequence` is the assembled restriction of `M`. -/
theorem principalPartsSequence_X₃ (M : ModuleCat.{u} B) :
    (principalPartsSequence A B M).X₃ = restrictedModule A B M :=
  sorry

/-- The simplicial first principal-parts sequence is short exact. -/
theorem principalPartsSequence_shortExact (M : ModuleCat.{u} B) :
    (principalPartsSequence A B M).ShortExact :=
  sorry

/-- Degreewise underived extension of scalars along the augmentations `P_n → B`. -/
def extensionMap (N : PresheafOfModules.{u} (standardSimplicialRing A B))
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (ModuleCat.extendScalars (augmentationHom A B n)).obj (N.obj n) ⟶
      (ModuleCat.extendScalars (augmentationHom A B m)).obj (N.obj m) :=
  ((ModuleCat.extendRestrictScalarsAdj (augmentationHom A B n)).homEquiv _ _).symm
    (N.map φ ≫
      (ModuleCat.restrictScalars (termMapHom A B φ)).map
        ((ModuleCat.extendRestrictScalarsAdj (augmentationHom A B m)).unit.app (N.obj m)) ≫
      (ModuleCat.restrictScalarsComp' (termMapHom A B φ) (augmentationHom A B m)
        (augmentationHom A B n) (termMapHom_comp_augmentationHom A B φ)).inv.app _)

/-- Degreewise underived extension of scalars along `P_• ⟶ B`, as a functor on simplicial
`P_•`-modules. Its left derived functor is derived tensor with `underline{B}`. -/
def extensionDegreewise :
    PresheafOfModules.{u} (standardSimplicialRing A B) ⥤
      (SimplexCategoryᵒᵖ ⥤ ModuleCat.{u} B) where
  obj N :=
    { obj n := (ModuleCat.extendScalars (augmentationHom A B n)).obj (N.obj n)
      map φ := extensionMap A B N φ
      map_id _ := sorry
      map_comp _ _ := sorry }
  map {N N'} f :=
    { app n := (ModuleCat.extendScalars (augmentationHom A B n)).map (f.app n)
      naturality _ _ _ := sorry }
  map_id _ := sorry
  map_comp _ _ := sorry

/-- Unfolding of `extensionDegreewise` on objects: degreewise `extendScalars` along the
augmentation. -/
theorem extensionDegreewise_obj_obj
    (N : PresheafOfModules.{u} (standardSimplicialRing A B)) (n : SimplexCategoryᵒᵖ) :
    ((extensionDegreewise A B).obj N).obj n =
      (ModuleCat.extendScalars (augmentationHom A B n)).obj (N.obj n) :=
  sorry

/-- The constant simplicial `B`-module with value `M`. -/
def simplicialConstant (M : ModuleCat.{u} B) :
    SimplicialObject (ModuleCat.{u} (under A B).right) :=
  (Functor.const _).obj M

/-- Unfolding of `simplicialConstant`. -/
theorem simplicialConstant_obj (M : ModuleCat.{u} B) (n : SimplexCategoryᵒᵖ) :
    (simplicialConstant A B M).obj n = M :=
  sorry

/-- The simplicial `B`-module `Ω_{P_n/A} ⊗_{P_n} B ⊗_B M`, using that the cotangent terms are
`P_n`-flat. -/
def simplicialCotangent (M : ModuleCat.{u} B) :
    SimplicialObject (ModuleCat.{u} B) where
  obj n :=
    (CommRingCat.Under.CotangentComplex.simplicialModule
        (CommRingCat.of A) (under A B)).obj n ⊗ M
  map φ :=
    (CommRingCat.Under.CotangentComplex.simplicialModuleMap
        (CommRingCat.of A) (under A B) φ) ▷ M
  map_id _ := sorry
  map_comp _ _ := sorry

/-- Degreewise, `simplicialCotangent` is the base change of `Ω_{P_n/A}` tensored with `M`. -/
theorem simplicialCotangent_obj (M : ModuleCat.{u} B) (n : SimplexCategoryᵒᵖ) :
    (simplicialCotangent A B M).obj n =
      (CommRingCat.Under.CotangentComplex.simplicialModule
          (CommRingCat.of A) (under A B)).obj n ⊗ M :=
  sorry

/-- The cochain complex of `B`-modules obtained from `simplicialCotangent`. This is the
standard-resolution model of `L_{B/A} ⊗_B M`. -/
def tensorCochain (M : ModuleCat.{u} B) : CochainComplex (ModuleCat.{u} B) ℤ :=
  ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
      (simplicialCotangent A B M)).extend ComplexShape.embeddingDownNat

/-- The cohomological degree `-n` term of `tensorCochain` is the `n`-th simplicial cotangent
tensor term. -/
def tensorCochain_X (M : ModuleCat.{u} B) (n : ℕ) :
    (tensorCochain A B M).X (-n) ≅ (simplicialCotangent A B M).obj (op (SimplexCategory.mk n)) :=
  extendXIso
    ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj (simplicialCotangent A B M))
    ComplexShape.embeddingDownNat (rfl : ComplexShape.embeddingDownNat.f n = -n)

/-- The cochain complex of `B`-modules obtained from the constant simplicial module `M`. -/
def constantComplex (M : ModuleCat.{u} B) : CochainComplex (ModuleCat.{u} B) ℤ :=
  ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
      (simplicialConstant A B M)).extend ComplexShape.embeddingDownNat

/-- The cohomological degree `-n` term of `constantComplex` is `M`. -/
def constantComplex_X (M : ModuleCat.{u} B) (n : ℕ) :
    (constantComplex A B M).X (-n) ≅ M :=
  extendXIso
    ((alternatingFaceMapComplex (ModuleCat.{u} B)).obj (simplicialConstant A B M))
    ComplexShape.embeddingDownNat (rfl : ComplexShape.embeddingDownNat.f n = -n)

/-- The degree-zero component of `constantToSingle` is the identification of the
simplicial value with `M`. -/
def constantComplex_X₀ (M : ModuleCat.{u} B) :
    (constantComplex A B M).X 0 ≅ M :=
  constantComplex_X A B M 0

/-- Differentials into degree `0` of `constantComplex` vanish after the identification with
`M`. -/
theorem constantToSingle_comp (M : ModuleCat.{u} B) (i : ℤ)
    (hi : ComplexShape.up ℤ |>.Rel i 0) :
    (constantComplex A B M).d i 0 ≫ (constantComplex_X₀ A B M).hom = 0 :=
  sorry

/-- The quasi-isomorphism from the evaluation complex of `underline{M}` to the single
complex of `M`. -/
def constantToSingle (M : ModuleCat.{u} B) :
    constantComplex A B M ⟶ (HomologicalComplex.single (ModuleCat.{u} B) (up ℤ) 0).obj M :=
  HomologicalComplex.mkHomToSingle (constantComplex_X₀ A B M).hom (constantToSingle_comp A B M)

/-- The degree-zero component of `singleToConstant` is the inverse identification with `M`. -/
theorem singleToConstant_comp (M : ModuleCat.{u} B) (k : ℤ)
    (hk : ComplexShape.up ℤ |>.Rel 0 k) :
    (constantComplex_X₀ A B M).inv ≫ (constantComplex A B M).d 0 k = 0 :=
  sorry

/-- The inverse comparison from the single complex of `M` to the evaluation complex of
`underline{M}`. -/
def singleToConstant (M : ModuleCat.{u} B) :
    (HomologicalComplex.single (ModuleCat.{u} B) (up ℤ) 0).obj M ⟶ constantComplex A B M :=
  HomologicalComplex.mkHomFromSingle (constantComplex_X₀ A B M).inv (singleToConstant_comp A B M)

end Algebra.CotangentComplex.Atiyah

end
