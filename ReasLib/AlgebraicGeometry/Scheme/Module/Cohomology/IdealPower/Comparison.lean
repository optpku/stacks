/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.Filtration
public import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.ArtinRees
public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism

/-!
# Ideal-power comparison for cohomology of complexes

This module packages the two shifted maps comparing the cohomology of the
termwise ideal-power subcomplexes with the ideal-power filtration on ambient
cohomology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

namespace IdealPowerComplex

/-- The degree-`p` cohomology object of the `n`th termwise ideal-power stage. -/
noncomputable abbrev homologyStage (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (p : ℤ) (n : ℕ) : X.Modules :=
  (HomologicalComplex.Filtered.Stage.complex (filtered I K) (n : ℤ)).homology p

/-- The canonical transition on the cohomology of termwise ideal-power stages. -/
noncomputable abbrev homologyTransition (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (p : ℤ) {m n : ℕ} (h : m ≤ n) :
    homologyStage I K p n ⟶ homologyStage I K p m :=
  HomologicalComplex.homologyMap
    (HomologicalComplex.Filtered.Stage.comparison (filtered I K) (Int.ofNat_le.mpr h)) p

/-- The canonical map from stage cohomology to the cohomology of the original complex. -/
noncomputable def toAmbient (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (p : ℤ) (n : ℕ) :
    homologyStage I K p n ⟶ K.homology p :=
  HomologicalComplex.Filtered.Homology.map (filtered I K) (n : ℤ) p ≫
    HomologicalComplex.homologyMap (underlyingIso I K).hom p

/-- Stage transitions commute with the canonical maps to ambient cohomology. -/
theorem homologyTransition_comp_toAmbient (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (p : ℤ) {m n : ℕ} (h : m ≤ n) :
    homologyTransition I K p h ≫ toAmbient I K p m = toAmbient I K p n := by
  have hs :
      HomologicalComplex.Filtered.Stage.comparison (filtered I K) (Int.ofNat_le.mpr h) ≫
          HomologicalComplex.Filtered.Stage.inclusion (filtered I K) (m : ℤ) =
        HomologicalComplex.Filtered.Stage.inclusion (filtered I K) (n : ℤ) := by
    apply HomologicalComplex.hom_ext
    intro i
    exact ((filtered I K).X i).filtration.inclusion_arrow (Int.ofNat_le.mpr h)
  dsimp [homologyTransition, toAmbient]
  rw [← Category.assoc]
  congr 1
  simpa only [HomologicalComplex.Filtered.Homology.map, HomologicalComplex.homologyMap_comp]
    using congrArg (fun f ↦ HomologicalComplex.homologyMap f p) hs

/-- The successor transition on cohomology of termwise ideal-power stages. -/
noncomputable abbrev homologyStep (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (p : ℤ) (n : ℕ) :
    homologyStage I K p (n + 1) ⟶ homologyStage I K p n :=
  homologyTransition I K p (Nat.le_succ n)

/-- The inverse system `n ↦ H^p(I^n K)`. -/
noncomputable def homologyTower (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (p : ℤ) :
    SequentialInverseSystem X.Modules :=
  Functor.ofOpSequence (fun n ↦ homologyStep I K p n)

/-- The object at index `n` of the termwise ideal-power cohomology tower. -/
theorem homologyTower_obj (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (p : ℤ) (n : ℕ) :
    (homologyTower I K p).obj (op n) = homologyStage I K p n := rfl

private theorem transitionMap_refl {C : Type*} [Category C]
    (F : SequentialInverseSystem C) (n : ℕ) :
    F.transitionMap (le_refl n) = 𝟙 (F.obj (op n)) :=
  F.map_id (op n)

private theorem transitionMap_succ_factor {C : Type*} [Category C]
    (F : SequentialInverseSystem C) {i k : ℕ} (h : i ≤ k) :
    F.transitionMap (Nat.le_succ_of_le h) = F.stepMap k ≫ F.transitionMap h :=
  F.map_comp (homOfLE (Nat.le_succ k)).op (homOfLE h).op

/-- Every transition in the cohomology tower is the canonical stage transition. -/
theorem homologyTower_transitionMap (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (p : ℤ) {m n : ℕ} (h : m ≤ n) :
    (homologyTower I K p).transitionMap h = homologyTransition I K p h := by
  induction n, h using Nat.le_induction (m := m) with
  | base =>
      rw [transitionMap_refl]
      change 𝟙 (homologyStage I K p m) = _
      have hs :
          HomologicalComplex.Filtered.Stage.comparison (filtered I K) (le_refl (m : ℤ)) =
            𝟙 (HomologicalComplex.Filtered.Stage.complex (filtered I K) (m : ℤ)) := by
        apply HomologicalComplex.hom_ext
        intro i
        exact ((filtered I K).X i).filtration.inclusion_refl _
      simp only [homologyTransition, hs, HomologicalComplex.homologyMap_id]
  | succ n h ih =>
      change (homologyTower I K p).transitionMap (Nat.le_succ_of_le h) =
        homologyTransition I K p (Nat.le_succ_of_le h)
      calc
        (homologyTower I K p).transitionMap (Nat.le_succ_of_le h) =
            (homologyTower I K p).stepMap n ≫
              (homologyTower I K p).transitionMap h :=
          transitionMap_succ_factor (homologyTower I K p) h
        _ = homologyStep I K p n ≫ homologyTransition I K p h := by
          rw [ih]
          congr 1
          simp [homologyTower, homologyStep]
        _ = homologyTransition I K p (Nat.le_succ_of_le h) := by
          dsimp [homologyStep, homologyTransition]
          have hmn : (m : ℤ) ≤ (n : ℤ) := Int.ofNat_le.mpr h
          have hns : (n : ℤ) ≤ ((n + 1 : ℕ) : ℤ) :=
            Int.ofNat_le.mpr (Nat.le_succ n)
          have hms : (m : ℤ) ≤ ((n + 1 : ℕ) : ℤ) :=
            Int.ofNat_le.mpr (Nat.le_succ_of_le h)
          change HomologicalComplex.homologyMap
              (HomologicalComplex.Filtered.Stage.comparison (filtered I K) hns) p ≫
              HomologicalComplex.homologyMap
              (HomologicalComplex.Filtered.Stage.comparison (filtered I K) hmn) p =
            HomologicalComplex.homologyMap
              (HomologicalComplex.Filtered.Stage.comparison (filtered I K) hms) p
          rw [← HomologicalComplex.homologyMap_comp]
          congr 1
          apply HomologicalComplex.hom_ext
          intro i
          exact ((filtered I K).X i).filtration.inclusion_trans hmn hns

/-- The `n`th ideal-power subobject of ambient cohomology. -/
noncomputable abbrev ambientStage (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (p : ℤ) (n : ℕ) : X.Modules :=
  ((IdealPowerFiltration.filtration I (K.homology p)).stage (n : ℤ) : X.Modules)

/-- The ambient stage at `n` is the existing ideal-power product subobject. -/
theorem ambientStage_eq (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (p : ℤ) (n : ℕ) :
    ambientStage I K p n = (idealPowerProductSubobject I (K.homology p) n : X.Modules) := rfl

/-- The inclusion between two ideal-power stages of ambient cohomology. -/
noncomputable abbrev ambientTransition (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (p : ℤ) {m n : ℕ} (h : m ≤ n) :
    ambientStage I K p n ⟶ ambientStage I K p m :=
  (IdealPowerFiltration.filtration I (K.homology p)).inclusion (Int.ofNat_le.mpr h)

/-- The inverse system `n ↦ I^n H^p(K)`. -/
noncomputable def ambientTower (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (p : ℤ) :
    SequentialInverseSystem X.Modules :=
  Functor.ofOpSequence (fun n ↦ ambientTransition I K p (Nat.le_succ n))

/-- The object at index `n` of the ambient ideal-power tower. -/
theorem ambientTower_obj (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (p : ℤ) (n : ℕ) :
    (ambientTower I K p).obj (op n) = ambientStage I K p n := rfl

/-- Every transition in the ambient tower is the canonical ideal-power inclusion. -/
theorem ambientTower_transitionMap (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (p : ℤ) {m n : ℕ} (h : m ≤ n) :
    (ambientTower I K p).transitionMap h = ambientTransition I K p h := by
  induction n, h using Nat.le_induction (m := m) with
  | base =>
      rw [transitionMap_refl]
      change 𝟙 (ambientStage I K p m) = _
      dsimp [ambientTransition]
      simp only [IndexedFiltration.inclusion_refl]
  | succ n h ih =>
      change (ambientTower I K p).transitionMap (Nat.le_succ_of_le h) =
        ambientTransition I K p (Nat.le_succ_of_le h)
      calc
        (ambientTower I K p).transitionMap (Nat.le_succ_of_le h) =
            (ambientTower I K p).stepMap n ≫
              (ambientTower I K p).transitionMap h :=
          transitionMap_succ_factor (ambientTower I K p) h
        _ = ambientTransition I K p (Nat.le_succ n) ≫ ambientTransition I K p h := by
          rw [ih]
          congr 1
          simpa only [ambientTower, SequentialInverseSystem.stepMap] using
            (Functor.ofOpSequence_map_homOfLE_succ
              (fun n ↦ ambientTransition I K p (Nat.le_succ n)) n)
        _ = ambientTransition I K p (Nat.le_succ_of_le h) := by
          dsimp [ambientTransition]
          have hmn : (m : ℤ) ≤ (n : ℤ) := Int.ofNat_le.mpr h
          have hns : (n : ℤ) ≤ ((n + 1 : ℕ) : ℤ) :=
            Int.ofNat_le.mpr (Nat.le_succ n)
          have hms : (m : ℤ) ≤ ((n + 1 : ℕ) : ℤ) :=
            Int.ofNat_le.mpr (Nat.le_succ_of_le h)
          change (IdealPowerFiltration.filtration I (K.homology p)).inclusion hns ≫
              (IdealPowerFiltration.filtration I (K.homology p)).inclusion hmn =
            (IdealPowerFiltration.filtration I (K.homology p)).inclusion hms
          exact IndexedFiltration.inclusion_trans _ hmn hns

end IdealPowerComplex

namespace IdealPowerCohomology

open IdealPowerComplex

/-- A shifted forward transformation is compatible with the maps to ambient cohomology. -/
def ForwardSpec (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ)
    (p : ℤ) (c : ℕ) (α : (homologyTower I K p).shift c ⟶ ambientTower I K p) : Prop :=
  ∀ n : ℕ,
    α.app (op n) ≫ (idealPowerProductSubobject I (K.homology p) n).arrow =
      toAmbient I K p (c + n)

/-- A shifted reverse transformation is canonical after mapping to ambient cohomology. -/
def ReverseSpec (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ)
    (p : ℤ) (c : ℕ) (β : (ambientTower I K p).shift c ⟶ homologyTower I K p) : Prop :=
  ∀ n : ℕ,
    β.app (op n) ≫ toAmbient I K p n =
      (idealPowerProductSubobject I (K.homology p) (c + n)).arrow

/-- Shifted comparison data between stage cohomology and ideal powers of ambient cohomology. -/
structure Comparison.{v} {X : Scheme.{v}} (I : X.IdealSheafData)
    (K : CochainComplex X.Modules ℤ) (p : ℤ) (c : ℕ) where
  /-- The shifted maps from stage cohomology to ideal powers of ambient cohomology. -/
  forward : (homologyTower I K p).shift c ⟶ ambientTower I K p
  /-- The shifted maps from ideal powers of ambient cohomology to stage cohomology. -/
  reverse : (ambientTower I K p).shift c ⟶ homologyTower I K p
  /-- Compatibility of the forward maps with ambient cohomology. -/
  forward_spec : ForwardSpec I K p c forward
  /-- Compatibility of the reverse maps with ambient cohomology. -/
  reverse_spec : ReverseSpec I K p c reverse
  /-- The two transformations are inverse after the two fixed shifts. -/
  isShiftedInverse : Pro.SequentialHom.IsShiftedInverse c c forward reverse

namespace Comparison

/-- Packages two shifted transformations and their compatibility laws as comparison data. -/
def ofShiftedMaps {I : X.IdealSheafData} {K : CochainComplex X.Modules ℤ}
    {p : ℤ} {c : ℕ}
    (forward : (homologyTower I K p).shift c ⟶ ambientTower I K p)
    (reverse : (ambientTower I K p).shift c ⟶ homologyTower I K p)
    (forward_spec : ForwardSpec I K p c forward)
    (reverse_spec : ReverseSpec I K p c reverse)
    (isShiftedInverse : Pro.SequentialHom.IsShiftedInverse c c forward reverse) :
    Comparison I K p c where
  forward := forward
  reverse := reverse
  forward_spec := forward_spec
  reverse_spec := reverse_spec
  isShiftedInverse := isShiftedInverse

/-- All defining conditions of a cohomology comparison, exposed together. -/
theorem spec {I : X.IdealSheafData} {K : CochainComplex X.Modules ℤ}
    {p : ℤ} {c : ℕ} (D : Comparison I K p c) :
    ForwardSpec I K p c D.forward ∧ ReverseSpec I K p c D.reverse ∧
      Pro.SequentialHom.IsShiftedInverse c c D.forward D.reverse :=
  ⟨D.forward_spec, D.reverse_spec, D.isShiftedInverse⟩

/-- Arithmetic bounds required for the two stable-range comparison composites. -/
theorem twoShiftBounds (c n : ℕ) (h : 2 * c ≤ n) :
    c ≤ n ∧ c ≤ n - c ∧ n - c - c ≤ n := by omega

/-- In the stable range, the image of `H^p(I^n K) ⟶ H^p(K)` lies in
`I^(n-c) H^p(K)`. -/
theorem imageBound {I : X.IdealSheafData} {K : CochainComplex X.Modules ℤ}
    {p : ℤ} {c : ℕ} (D : Comparison I K p c) (n : ℕ) (h : c ≤ n) :
    imageSubobject (toAmbient I K p n) ≤
      idealPowerProductSubobject I (K.homology p) (n - c) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  apply imageSubobject_le (toAmbient I K p (c + k)) (D.forward.app (op k))
  exact D.forward_spec k

/-- The canonical factor `H^p(I^n K) ⟶ I^(n-c) H^p(K)` in the stable range. -/
noncomputable def forwardAt {I : X.IdealSheafData} {K : CochainComplex X.Modules ℤ}
    {p : ℤ} {c : ℕ} (D : Comparison I K p c) (n : ℕ) (h : c ≤ n) :
    homologyStage I K p n ⟶ ambientStage I K p (n - c) :=
  eqToHom (congrArg (homologyStage I K p) (Nat.add_sub_of_le h).symm) ≫
    D.forward.app (op (n - c))

-- Retain the object equality as a parameter to reuse the opaque proofs in the `eq_def` lemmas.
private theorem factor_comp {C : Type*} [Category C]
    (F G : ℕ → C) (B : C) (c : ℕ)
    (α : ∀ k, F (c + k) ⟶ G k) (a : ∀ k, G k ⟶ B) (b : ∀ k, F k ⟶ B)
    (hs : ∀ k, α k ≫ a k = b (c + k)) (n k : ℕ)
    (en : n = c + k) (e : F n = F (c + k)) :
    (eqToHom e ≫ α k) ≫ a k = b n := by
  subst n
  simpa only [eqToHom_refl, Category.id_comp] using hs k

/-- Composing the stable-range forward factor with the ideal-power inclusion recovers the
ambient cohomology map. -/
theorem forwardAt_comp_arrow {I : X.IdealSheafData} {K : CochainComplex X.Modules ℤ}
    {p : ℤ} {c : ℕ} (D : Comparison I K p c) (n : ℕ) (h : c ≤ n) :
    D.forwardAt n h ≫ (idealPowerProductSubobject I (K.homology p) (n - c)).arrow =
      toAmbient I K p n := by
  refine (congrArg
    (fun f ↦ f ≫ (idealPowerProductSubobject I (K.homology p) (n - c)).arrow)
    (forwardAt.eq_def D n h)).trans ?_
  apply factor_comp (homologyStage I K p) (ambientStage I K p) (K.homology p) c
    (fun k ↦ D.forward.app (op k))
    (fun k ↦ (idealPowerProductSubobject I (K.homology p) k).arrow)
    (toAmbient I K p) D.forward_spec n (n - c) (Nat.add_sub_of_le h).symm

/-- The canonical map `I^n H^p(K) ⟶ H^p(I^(n-c)K)` in the stable range. -/
noncomputable def reverseAt {I : X.IdealSheafData} {K : CochainComplex X.Modules ℤ}
    {p : ℤ} {c : ℕ} (D : Comparison I K p c) (n : ℕ) (h : c ≤ n) :
    ambientStage I K p n ⟶ homologyStage I K p (n - c) :=
  eqToHom (congrArg (ambientStage I K p) (Nat.add_sub_of_le h).symm) ≫
    D.reverse.app (op (n - c))

/-- The stable-range reverse map has the canonical composite into ambient cohomology. -/
theorem reverseAt_comp_toAmbient {I : X.IdealSheafData}
    {K : CochainComplex X.Modules ℤ} {p : ℤ} {c : ℕ}
    (D : Comparison I K p c) (n : ℕ) (h : c ≤ n) :
    D.reverseAt n h ≫ toAmbient I K p (n - c) =
      (idealPowerProductSubobject I (K.homology p) n).arrow := by
  refine (congrArg (fun f ↦ f ≫ toAmbient I K p (n - c))
    (reverseAt.eq_def D n h)).trans ?_
  apply factor_comp (ambientStage I K p) (homologyStage I K p) (K.homology p) c
    (fun k ↦ D.reverse.app (op k)) (toAmbient I K p)
    (fun k ↦ (idealPowerProductSubobject I (K.homology p) k).arrow)
    D.reverse_spec n (n - c) (Nat.add_sub_of_le h).symm

private theorem pair_comp {C : Type*} [Category C]
    (F G : ℕ → C) (c : ℕ)
    (α : ∀ k, F (c + k) ⟶ G k) (β : ∀ k, G (c + k) ⟶ F k)
    (T : ∀ {i j : ℕ}, i ≤ j → (F j ⟶ F i))
    (hs : ∀ k, α (c + k) ≫ β k = T (Pro.SequentialHom.shift_le c c k))
    (n m k : ℕ) (en : n = c + m) (em : m = c + k) (hkn : k ≤ n)
    (e : F n = F (c + m)) (e' : G m = G (c + k)) :
    (eqToHom e ≫ α m) ≫ (eqToHom e' ≫ β k) = T hkn := by
  subst n
  subst m
  simpa only [eqToHom_refl, Category.id_comp] using hs k

/-- The reverse map followed by the forward factor is the canonical ambient-tower transition. -/
theorem reverse_forward {I : X.IdealSheafData} {K : CochainComplex X.Modules ℤ}
    {p : ℤ} {c : ℕ} (D : Comparison I K p c) (n : ℕ) (h : 2 * c ≤ n) :
    D.reverseAt n (twoShiftBounds c n h).1 ≫
        D.forwardAt (n - c) (twoShiftBounds c n h).2.1 =
      ambientTransition I K p (twoShiftBounds c n h).2.2 := by
  refine (congrArg₂ (fun f g ↦ f ≫ g)
    (reverseAt.eq_def D n (twoShiftBounds c n h).1)
    (forwardAt.eq_def D (n - c) (twoShiftBounds c n h).2.1)).trans ?_
  apply pair_comp (ambientStage I K p) (homologyStage I K p) c
    (fun k ↦ D.reverse.app (op k)) (fun k ↦ D.forward.app (op k))
    (fun {_ _} h ↦ ambientTransition I K p h)
    (fun k ↦ (D.isShiftedInverse.2 k).trans (ambientTower_transitionMap I K p _))
    n (n - c) (n - c - c) (Nat.add_sub_of_le (twoShiftBounds c n h).1).symm
    (Nat.add_sub_of_le (twoShiftBounds c n h).2.1).symm (twoShiftBounds c n h).2.2

/-- The forward factor followed by the reverse map is the canonical cohomology-tower
transition. -/
theorem forward_reverse {I : X.IdealSheafData} {K : CochainComplex X.Modules ℤ}
    {p : ℤ} {c : ℕ} (D : Comparison I K p c) (n : ℕ) (h : 2 * c ≤ n) :
    D.forwardAt n (twoShiftBounds c n h).1 ≫
        D.reverseAt (n - c) (twoShiftBounds c n h).2.1 =
      homologyTransition I K p (twoShiftBounds c n h).2.2 := by
  refine (congrArg₂ (fun f g ↦ f ≫ g)
    (forwardAt.eq_def D n (twoShiftBounds c n h).1)
    (reverseAt.eq_def D (n - c) (twoShiftBounds c n h).2.1)).trans ?_
  apply pair_comp (homologyStage I K p) (ambientStage I K p) c
    (fun k ↦ D.forward.app (op k)) (fun k ↦ D.reverse.app (op k))
    (fun {_ _} h ↦ homologyTransition I K p h)
    (fun k ↦ (D.isShiftedInverse.1 k).trans (homologyTower_transitionMap I K p _))
    n (n - c) (n - c - c) (Nat.add_sub_of_le (twoShiftBounds c n h).1).symm
    (Nat.add_sub_of_le (twoShiftBounds c n h).2.1).symm (twoShiftBounds c n h).2.2

/-- The explicit isomorphism of pro-objects determined by a cohomology comparison. -/
noncomputable abbrev toProIso {I : X.IdealSheafData} {K : CochainComplex X.Modules ℤ}
    {p : ℤ} {c : ℕ} (D : Comparison I K p c) :
    (Pro.lim (C := X.Modules) ℕᵒᵖ).obj (homologyTower I K p) ≅
      (Pro.lim (C := X.Modules) ℕᵒᵖ).obj (ambientTower I K p) :=
  D.isShiftedInverse.iso

end Comparison

/-- A Noetherian scheme and a termwise coherent complex admit an eventual ideal-power
cohomology comparison. -/
theorem existsComparison {X : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
    (I : X.IdealSheafData) (K : CochainComplex X.Modules ℤ)
    [∀ i : ℤ, (K.X i).IsCoherent] (p : ℤ) :
    ∃ c : ℕ, ∃ D : Comparison I K p c, 0 < c := sorry

end IdealPowerCohomology

end AlgebraicGeometry.Scheme.Modules
