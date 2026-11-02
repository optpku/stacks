/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
    intersectionOpen f σ ≤ intersectionOpen f (σ.delete j) := by
  exact le_iInf fun a ↦ iInf_le (fun b ↦ PrimeSpectrum.basicOpen (f (σ b)))
    (j.succAbove a)

/-- Restriction of sections from a deleted strict tuple to the full tuple. -/
noncomputable def restriction (f : Fin r → A) (F : (affineRingedSpace A).Modules)
    {p : ℕ} (σ : OrderedCechIndex (Fin r) (p + 1)) (j : Fin (p + 2)) :
    sectionModule f F (σ.delete j) ⟶ sectionModule f F σ :=
  (OverGlobal.restrictionOfLE (intersectionOpen_le_delete f σ j)).app F

/-- Degree `p` of the strict principal-open alternating Cech complex. -/
abbrev term (f : Fin r → A) (F : (affineRingedSpace A).Modules) (p : ℕ) :
    ModuleCat (RingedSpace.globalSectionsRing (affineRingedSpace A)) :=
  ∏ᶜ fun σ : OrderedCechIndex (Fin r) p ↦ sectionModule f F σ

private theorem restrictionOfLE_comp {U V W : TopologicalSpace.Opens (affineRingedSpace A).carrier}
    (hUV : U ≤ V) (hVW : V ≤ W) (F : (affineRingedSpace A).Modules) :
    (OverGlobal.restrictionOfLE hVW).app F ≫
        (OverGlobal.restrictionOfLE hUV).app F =
      (OverGlobal.restrictionOfLE (hUV.trans hVW)).app F := by
  ext x
  change F.val.map (CategoryTheory.homOfLE hUV).op
      (F.val.map (CategoryTheory.homOfLE hVW).op x) =
    F.val.map (CategoryTheory.homOfLE (hUV.trans hVW)).op x
  rw [← F.val.map_comp_apply]
  rfl

/-- The `j`th coface on strictly indexed principal-open Cech terms. -/
noncomputable def coface (f : Fin r → A) (F : (affineRingedSpace A).Modules)
    (p : ℕ) (j : Fin (p + 2)) : term f F p ⟶ term f F (p + 1) :=
  Limits.Pi.map' (fun σ : OrderedCechIndex (Fin r) (p + 1) ↦ σ.delete j)
    (fun σ ↦ restriction f F σ j)

set_option backward.isDefEq.respectTransparency false in
private theorem coface_comp (f : Fin r → A) (F : (affineRingedSpace A).Modules)
    (p : ℕ) (i : Fin (p + 2)) (j : Fin (p + 3)) (h : j.val ≤ i.val) :
    coface f F p i ≫ coface f F (p + 1) j =
      coface f F p (Fin.castLT j (lt_of_le_of_lt h i.isLt)) ≫
        coface f F (p + 1) i.succ := by
  have hdel (σ : OrderedCechIndex (Fin r) (p + 2)) :
      (σ.delete j).delete i =
        (σ.delete i.succ).delete (Fin.castLT j (lt_of_le_of_lt h i.isLt)) := by
    apply DFunLike.ext
    intro a
    change σ (j.succAbove (i.succAbove a)) =
      σ (i.succ.succAbove ((Fin.castLT j (lt_of_le_of_lt h i.isLt)).succAbove a))
    congr 1
    apply Fin.ext
    simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, Fin.val_succ, Fin.val_castLT,
      apply_ite Fin.val]
    split_ifs <;> omega
  apply Limits.Pi.hom_ext
  intro σ
  simp only [coface, Category.assoc, Limits.Pi.map'_comp_π,
    Limits.Pi.map'_comp_π_assoc, restriction, restrictionOfLE_comp]
  have heq (τ τ' : OrderedCechIndex (Fin r) p) (e : τ = τ')
      (hτ : intersectionOpen f σ ≤ intersectionOpen f τ)
      (hτ' : intersectionOpen f σ ≤ intersectionOpen f τ') :
      Limits.Pi.π (fun τ : OrderedCechIndex (Fin r) p ↦ sectionModule f F τ) τ ≫
          (OverGlobal.restrictionOfLE hτ).app F =
        Limits.Pi.π (fun τ : OrderedCechIndex (Fin r) p ↦ sectionModule f F τ) τ' ≫
          (OverGlobal.restrictionOfLE hτ').app F := by
    subst τ'
    rfl
  exact heq _ _ (hdel σ) _ _

/-- The alternating restriction differential on strictly indexed principal-open Cech terms. -/
noncomputable def differential (f : Fin r → A) (F : (affineRingedSpace A).Modules)
    (p : ℕ) : term f F p ⟶ term f F (p + 1) :=
  ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • coface f F p j

set_option backward.isDefEq.respectTransparency false in
/-- Consecutive strict principal-open alternating Cech differentials compose to zero. -/
theorem differential_comp (f : Fin r → A) (F : (affineRingedSpace A).Modules)
    (p : ℕ) : differential f F p ≫ differential f F (p + 1) = 0 := by
  unfold differential
  rw [Preadditive.sum_comp]
  simp only [Preadditive.comp_sum, ← Finset.sum_product']
  -- Pair the two orders of deleting each pair of coordinates.
  let P := Fin (p + 2) × Fin (p + 3)
  let S : Finset P := {ij : P | (ij.2 : ℕ) ≤ (ij.1 : ℕ)}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S,
    ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij ↦
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right ij.1.isLt), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using congrArg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using congrArg Fin.castSucc (congrArg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, Fin.val_castLT, pow_add, pow_one, mul_neg,
        neg_mul, neg_neg, mul_one]
      apply mul_comm
    · exact coface_comp f F p i j (by simpa [S] using hij)

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
      (complex f F).d p q ≫ termMap f g q := by
  by_cases hpq : p + 1 = q
  · subst q
    simp only [complex, CochainComplex.of_d, differential, Preadditive.comp_sum,
      Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    simp only [termMap, coface, Limits.Pi.map_comp_map', Limits.Pi.map'_comp_map]
    congr 1
    funext σ
    exact (OverGlobal.restrictionOfLE (intersectionOpen_le_delete f σ j)).naturality g
  · rw [(complex f G).shape p q hpq, (complex f F).shape p q hpq]
    change termMap f g p ≫ (0 : term f G p ⟶ term f G q) =
      (0 : term f F p ⟶ term f F q) ≫ termMap f g q
    simp only [Limits.comp_zero, Limits.zero_comp]

/-- The map of strict principal-open alternating Cech complexes induced by a module-sheaf map. -/
noncomputable def complexMap (f : Fin r → A) {F G : (affineRingedSpace A).Modules}
    (g : F ⟶ G) : complex f F ⟶ complex f G where
  f p := termMap f g p
  comm' := fun _ _ _ ↦ termMap_comm f g

/-- The strict alternating Cech-complex map induced by an identity is the identity. -/
theorem complexMap_id (f : Fin r → A) (F : (affineRingedSpace A).Modules) :
    complexMap f (𝟙 F) = 𝟙 (complex f F) := by
  apply HomologicalComplex.Hom.ext
  funext p
  change termMap f (𝟙 F) p = 𝟙 (term f F p)
  unfold termMap
  have h : (fun σ : OrderedCechIndex (Fin r) p ↦
      (OverGlobal.functor (affineRingedSpace A) (intersectionOpen f σ)).map (𝟙 F)) =
      (fun σ ↦ 𝟙 (sectionModule f F σ)) := by
    funext σ
    exact (OverGlobal.functor (affineRingedSpace A) (intersectionOpen f σ)).map_id F
  rw [h, Limits.Pi.map_id]

/-- Strict alternating Cech-complex maps respect composition. -/
theorem complexMap_comp (f : Fin r → A) {F G H : (affineRingedSpace A).Modules}
    (g : F ⟶ G) (h : G ⟶ H) :
    complexMap f (g ≫ h) = complexMap f g ≫ complexMap f h := by
  apply HomologicalComplex.Hom.ext
  funext p
  change termMap f (g ≫ h) p = termMap f g p ≫ termMap f h p
  simp only [termMap, Functor.map_comp, Limits.Pi.map_comp_map]

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
    (complexFunctor f).PreservesZeroMorphisms where
  map_zero F G := by
    apply HomologicalComplex.Hom.ext
    funext p
    change termMap f (0 : F ⟶ G) p = 0
    apply Limits.Pi.hom_ext
    intro σ
    simp only [termMap, Limits.Pi.map_π, Functor.map_zero, Limits.comp_zero, Limits.zero_comp]

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
    (σ : OrderedCechIndex (Fin r) 0) : intersectionOpen f σ ≤ openSubset f := by
  change (⨅ a, PrimeSpectrum.basicOpen (f (σ a))) ≤
    (⨆ i, PrimeSpectrum.basicOpen (f i))
  calc
    (⨅ a, PrimeSpectrum.basicOpen (f (σ a))) ≤ PrimeSpectrum.basicOpen (f (σ 0)) :=
      iInf_le _ 0
    _ ≤ (⨆ i, PrimeSpectrum.basicOpen (f i)) := le_iSup (fun i ↦ PrimeSpectrum.basicOpen (f i)) (σ 0)

/-- Restriction from the principal-open union to the degree-zero strict Cech term. -/
noncomputable def augmentationMap (f : Fin r → A) (F : (affineRingedSpace A).Modules) :
    (sectionsOnUnion f).obj F ⟶ term f F 0 :=
  Limits.Pi.lift fun σ ↦
    (OverGlobal.restrictionOfLE (intersectionOpen_le_openSubset f σ)).app F

/-- The degree-zero restriction map is natural in the module sheaf. -/
theorem augmentationMap_naturality (f : Fin r → A)
    {F G : (affineRingedSpace A).Modules} (g : F ⟶ G) :
    (sectionsOnUnion f).map g ≫ augmentationMap f G =
      augmentationMap f F ≫ termMap f g 0 := by
  apply Limits.Pi.hom_ext
  intro σ
  simp only [augmentationMap, termMap, Category.assoc, Limits.Pi.lift_π,
    Limits.Pi.map_π, Limits.Pi.lift_π_assoc]
  exact (OverGlobal.restrictionOfLE (intersectionOpen_le_openSubset f σ)).naturality g

set_option backward.isDefEq.respectTransparency false in
private theorem augmentationMap_comp_differential (f : Fin r → A)
    (F : (affineRingedSpace A).Modules) :
    augmentationMap f F ≫ differential f F 0 = 0 := by
  apply Limits.Pi.hom_ext
  intro σ
  simp only [differential, Preadditive.comp_sum, Preadditive.comp_zsmul]
  rw [Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, Category.assoc, Limits.zero_comp]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
    neg_zsmul]
  have h0 := restrictionOfLE_comp
    (intersectionOpen_le_delete f σ 0)
    (intersectionOpen_le_openSubset f (σ.delete 0)) F
  have h1 := restrictionOfLE_comp
    (intersectionOpen_le_delete f σ 1)
    (intersectionOpen_le_openSubset f (σ.delete 1)) F
  simp only [coface, Limits.Pi.map'_comp_π, augmentationMap, Limits.Pi.lift_π_assoc,
    restriction]
  rw [h0, h1]
  simp

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

set_option backward.isDefEq.respectTransparency false in
private theorem augmentationMap_extend_naturality (f : Fin r → A)
    {F G : (affineRingedSpace A).Modules} (g : F ⟶ G) :
    (augmentationMap f F ≫
      ((complex f F).extendXIso embeddingUpNat embeddingUpNat_zero).inv) ≫
        (HomologicalComplex.extendMap (complexMap f g) embeddingUpNat).f 0 =
      (sectionsOnUnion f).map g ≫ augmentationMap f G ≫
        ((complex f G).extendXIso embeddingUpNat embeddingUpNat_zero).inv := by
  rw [HomologicalComplex.extendMap_f _ _ embeddingUpNat_zero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change augmentationMap f F ≫ termMap f g 0 ≫
      ((complex f G).extendXIso embeddingUpNat embeddingUpNat_zero).inv = _
  rw [← Category.assoc, ← augmentationMap_naturality f g, Category.assoc]

/-- The degreewise union-to-Cech restrictions commute with the differential of the sheaf
complex. -/
theorem augmentationZeroRowComponent_comm (f : Fin r → A)
    (K : CochainComplex (affineRingedSpace A).Modules ℤ) {n n' : ℤ}
    (hnn' : (up ℤ).Rel n n') :
    augmentationZeroRowComponent f K n ≫ (zeroRow f K).d n n' =
      (((sectionsOnUnion f).mapHomologicalComplex (up ℤ)).obj K).d n n' ≫
        augmentationZeroRowComponent f K n' := by
  clear hnn'
  exact augmentationMap_extend_naturality f (K.d n n')

/-- The section restrictions assemble into the zero row of the strict alternating Cech
bicomplex. -/
noncomputable def augmentationZeroRow (f : Fin r → A)
    (K : CochainComplex (affineRingedSpace A).Modules ℤ) :
    ((sectionsOnUnion f).mapHomologicalComplex (up ℤ)).obj K ⟶ zeroRow f K where
  f n := augmentationZeroRowComponent f K n
  comm' := fun _ _ h ↦ augmentationZeroRowComponent_comm f K h

set_option backward.isDefEq.respectTransparency false in
/-- The degree-zero strict Cech augmentation lands in vertical cycles. -/
theorem augmentationZeroRow_cycles (f : Fin r → A)
    (K : CochainComplex (affineRingedSpace A).Modules ℤ) :
    ∀ n : ℤ, (augmentationZeroRow f K).f n ≫
      ((((row f).mapHomologicalComplex (up ℤ)).obj K).X n).d 0 1 = 0 := by
  intro n
  change (augmentationMap f (K.X n) ≫
      ((complex f (K.X n)).extendXIso embeddingUpNat rfl).inv) ≫
      ((complex f (K.X n)).extend embeddingUpNat).d
        (embeddingUpNat.f 0) (embeddingUpNat.f 1) = 0
  rw [HomologicalComplex.extend_d_eq (K := complex f (K.X n))
    (e := embeddingUpNat) (i := 0) (j := 1) rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change augmentationMap f (K.X n) ≫ (complex f (K.X n)).d 0 1 ≫ _ = 0
  have hd : (complex f (K.X n)).d 0 1 = differential f (K.X n) 0 :=
    CochainComplex.of_d (term f (K.X n)) (differential f (K.X n)) 0
  rw [hd, ← Category.assoc, augmentationMap_comp_differential, Limits.zero_comp]

/-- The canonical augmentation from sections on the principal-open union to the total strict
alternating Cech complex. -/
noncomputable def augmentation (f : Fin r → A)
    (K : CochainComplex (affineRingedSpace A).Modules ℤ) :
    ((sectionsOnUnion f).mapHomologicalComplex (up ℤ)).obj K ⟶ (total f).obj K :=
  ZeroRow.ToTotal.map (augmentationZeroRow f K) (augmentationZeroRow_cycles f K)

set_option backward.isDefEq.respectTransparency false in
/-- The total strict alternating Cech augmentation is natural in the sheaf complex. -/
theorem augmentation_naturality (f : Fin r → A)
    {K L : CochainComplex (affineRingedSpace A).Modules ℤ} (g : K ⟶ L) :
    ((sectionsOnUnion f).mapHomologicalComplex (up ℤ)).map g ≫ augmentation f L =
      augmentation f K ≫ (total f).map g := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (sectionsOnUnion f).map (g.f n) ≫
      (augmentationZeroRowComponent f L n ≫ _) =
    (augmentationZeroRowComponent f K n ≫ _) ≫
      (HomologicalComplex₂.total.map (((row f).mapHomologicalComplex (up ℤ)).map g)
        (up ℤ)).f n
  simp only [Category.assoc, HomologicalComplex₂.ιTotal_map]
  change (sectionsOnUnion f).map (g.f n) ≫
      (augmentationZeroRowComponent f L n ≫
        HomologicalComplex₂.ιTotal (((row f).mapHomologicalComplex (up ℤ)).obj L)
          (up ℤ) n 0 n (Int.add_zero n)) =
    augmentationZeroRowComponent f K n ≫
      (HomologicalComplex.extendMap (complexMap f (g.f n)) embeddingUpNat).f 0 ≫
        HomologicalComplex₂.ιTotal (((row f).mapHomologicalComplex (up ℤ)).obj L)
          (up ℤ) n 0 n (Int.add_zero n)
  exact congrArg (fun k ↦ k ≫
    HomologicalComplex₂.ιTotal (((row f).mapHomologicalComplex (up ℤ)).obj L)
      (up ℤ) n 0 n (Int.add_zero n))
    (augmentationMap_extend_naturality f (g.f n)).symm

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
