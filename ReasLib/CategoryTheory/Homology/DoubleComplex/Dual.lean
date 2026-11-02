/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Matress

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

namespace HomologicalComplex₂

variable {k : Type u} [Field k]

/-- The double complex obtained by forgetting the scalar multiplication. -/
def forgetModule (K : HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ)) :
    HomologicalComplex₂ AddCommGrpCat.{u} (up ℤ) (up ℤ) :=
  (((forget₂ (ModuleCat.{u} k) AddCommGrpCat).mapHomologicalComplex (up ℤ)).mapHomologicalComplex
    (up ℤ)).obj K

/-- A `k`-linear double complex is a matress when its additive image is one. -/
def ModuleMatress (K : HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ))
    (period : K ≅ K.bidegreeShift 3 (-3)) : Prop :=
  let F :=
    ((forget₂ (ModuleCat.{u} k) AddCommGrpCat).mapHomologicalComplex (up ℤ)).mapHomologicalComplex
      (up ℤ)
  HomologicalComplex₂.Matress (forgetModule K) (F.mapIso period)

/-- The oppositely indexed termwise dual double complex. -/
def dualComplex (K : HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ)) :
    HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ) :=
  HomologicalComplex₂.ofGradedObject (up ℤ) (up ℤ)
    (fun ⟨p, q⟩ => ModuleCat.of k (Module.Dual k ((K.X (-q)).X (-p))))
    (fun p p' q =>
      ModuleCat.ofHom (((K.X (-q)).d (-p') (-p)).hom.dualMap))
    (fun p q q' =>
      ModuleCat.ofHom (((K.d (-q') (-q)).f (-p)).hom.dualMap))
    (by
      intro p p' hp q
      have hp' : ¬ (up ℤ).Rel (-p') (-p) := by
        change ¬ (-p' + 1 = -p)
        change ¬ (p + 1 = p') at hp
        omega
      rw [(K.X (-q)).shape _ _ hp']
      ext φ x
      simp)
    (by
      intro p q q' hq
      have hq' : ¬ (up ℤ).Rel (-q') (-q) := by
        change ¬ (-q' + 1 = -q)
        change ¬ (q + 1 = q') at hq
        omega
      rw [K.shape _ _ hq', HomologicalComplex.zero_f]
      ext φ x
      simp)
    (by
      intro p p' p'' q
      apply ModuleCat.hom_ext
      change (((K.X (-q)).d (-p'') (-p')).hom.dualMap.comp
        (((K.X (-q)).d (-p') (-p)).hom.dualMap)) = 0
      rw [LinearMap.dualMap_comp_dualMap, ← ModuleCat.hom_comp,
        HomologicalComplex.d_comp_d]
      ext φ x
      simp)
    (by
      intro p q q' q''
      apply ModuleCat.hom_ext
      change (((K.d (-q'') (-q')).f (-p)).hom.dualMap.comp
        (((K.d (-q') (-q)).f (-p)).hom.dualMap)) = 0
      rw [LinearMap.dualMap_comp_dualMap, ← ModuleCat.hom_comp, K.d_f_comp_d_f]
      ext φ x
      simp)
    (by
      intro p p' q q'
      apply ModuleCat.hom_ext
      change (((K.d (-q') (-q)).f (-p')).hom.dualMap.comp
        (((K.X (-q)).d (-p') (-p)).hom.dualMap)) =
          (((K.X (-q')).d (-p') (-p)).hom.dualMap.comp
            (((K.d (-q') (-q)).f (-p)).hom.dualMap))
      rw [LinearMap.dualMap_comp_dualMap, LinearMap.dualMap_comp_dualMap,
        ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, HomologicalComplex.Hom.comm])

namespace ModuleMatress

private lemma dualPeriodIso_transport {C : Type*} [Category C]
    {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) (hW : W = Y) (hX : X = Z)
    (hfg : HEq f g) : eqToHom hW ≫ g = f ≫ eqToHom hX := by
  subst hW
  subst hX
  cases eq_of_heq hfg
  simp

private lemma dualPeriodIso_component_eq
    (K : HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ)) (p q : ℤ) :
    ModuleCat.of k (Module.Dual k (((K.bidegreeShift 3 (-3)).X (-q)).X (-p))) =
      (((dualComplex K).bidegreeShift 3 (-3)).X p).X q := by
  change ModuleCat.of k (Module.Dual k ((K.X (-q + 3)).X (-p - 3))) =
    ModuleCat.of k (Module.Dual k ((K.X (-(q + -3))).X (-(p + 3))))
  exact congrArg (fun i : ℤ × ℤ => ModuleCat.of k (Module.Dual k ((K.X i.1).X i.2)))
    (show (-q + 3, -p - 3) = (-(q + -3), -(p + 3)) by
      apply Prod.ext <;> omega)

private lemma dualPeriodIso_dualMap_square {A B C D : ModuleCat.{u} k}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D) (h : a ≫ b = c ≫ d) :
    ModuleCat.ofHom d.hom.dualMap ≫ ModuleCat.ofHom c.hom.dualMap =
      ModuleCat.ofHom b.hom.dualMap ≫ ModuleCat.ofHom a.hom.dualMap := by
  apply ModuleCat.hom_ext
  change c.hom.dualMap.comp d.hom.dualMap = a.hom.dualMap.comp b.hom.dualMap
  rw [LinearMap.dualMap_comp_dualMap, LinearMap.dualMap_comp_dualMap,
    ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, h]

private lemma dualPeriodIso_d₁
    (K : HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ)) (p p' q : ℤ) :
    HEq (ModuleCat.ofHom
      ((((K.bidegreeShift 3 (-3)).X (-q)).d (-p') (-p)).hom.dualMap))
      ((((dualComplex K).bidegreeShift 3 (-3)).d p p').f q) := by
  change HEq
    (ModuleCat.ofHom ((((-3 : ℤ).negOnePow •
      (K.X (-q + 3)).d (-p' + -3) (-p + -3))).hom.dualMap))
    ((3 : ℤ).negOnePow • ModuleCat.ofHom
      (((K.X (-(q + -3))).d (-(p' + 3)) (-(p + 3))).hom.dualMap))
  simp only [Int.negOnePow_neg, show (3 : ℤ).negOnePow = -1 by decide,
    Units.neg_smul, one_smul, ModuleCat.hom_neg, LinearMap.dualMap_def, map_neg]
  change HEq (-ModuleCat.ofHom (Module.Dual.transpose
    (((K.X (-q + 3)).d (-p' + -3) (-p + -3)).hom))) _
  let F := fun (i : ℤ × ℤ × ℤ) =>
    -ModuleCat.ofHom (Module.Dual.transpose (((K.X i.1).d i.2.1 i.2.2).hom))
  have hF : ∀ i j : ℤ × ℤ × ℤ, i = j → HEq (F i) (F j) := by
    intro i j hij
    subst j
    rfl
  exact hF (-q + 3, -p' + -3, -p + -3)
    (-(q + -3), -(p' + 3), -(p + 3)) (by
      apply Prod.ext
      · omega
      · apply Prod.ext <;> dsimp <;> omega)

private lemma dualPeriodIso_d₂
    (K : HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ)) (p q q' : ℤ) :
    HEq (ModuleCat.ofHom
      ((((K.bidegreeShift 3 (-3)).d (-q') (-q)).f (-p)).hom.dualMap))
      ((((dualComplex K).bidegreeShift 3 (-3)).X p).d q q') := by
  change HEq
    (ModuleCat.ofHom
      ((((K.bidegreeShift 3 (-3)).d (-q') (-q)).f (-p)).hom.dualMap))
    ((-3 : ℤ).negOnePow • ModuleCat.ofHom
      (((K.d (-(q' + -3)) (-(q + -3))).f (-(p + 3))).hom.dualMap))
  dsimp [bidegreeShift]
  simp only [Functor.mapHomologicalComplex_obj_d, CochainComplex.shiftFunctor_map_f']
  change HEq
    (ModuleCat.ofHom (((3 : ℤ).negOnePow •
      ((K.d (-q' + 3) (-q + 3)).f (-p + -3))).hom.dualMap)) _
  simp only [show (3 : ℤ).negOnePow = -1 by decide,
    show (-3 : ℤ).negOnePow = -1 by decide, Units.neg_smul, one_smul,
    ModuleCat.hom_neg, LinearMap.dualMap_def, map_neg]
  change HEq (-ModuleCat.ofHom (Module.Dual.transpose
    (((K.d (-q' + 3) (-q + 3)).f (-p + -3)).hom))) _
  let F := fun (i : ℤ × ℤ × ℤ) =>
    -ModuleCat.ofHom (Module.Dual.transpose (((K.d i.1 i.2.1).f i.2.2).hom))
  have hF : ∀ i j : ℤ × ℤ × ℤ, i = j → HEq (F i) (F j) := by
    intro i j hij
    subst j
    rfl
  exact hF (-q' + 3, -q + 3, -p + -3)
    (-(q' + -3), -(q + -3), -(p + 3)) (by
      apply Prod.ext
      · dsimp
        omega
      · apply Prod.ext <;> dsimp <;> omega)

/-- The canonical signed period isomorphism on the oppositely indexed dual. -/
def dualPeriodIso (K : HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ))
    (period : K ≅ K.bidegreeShift 3 (-3)) :
    dualComplex K ≅ (dualComplex K).bidegreeShift 3 (-3) := by
  let raw : dualComplex K ≅ (dualComplex K).bidegreeShift 3 (-3) :=
    { hom := HomologicalComplex₂.homMk
        (fun ⟨p, q⟩ =>
          ModuleCat.ofHom (((period.inv.f (-q)).f (-p)).hom.dualMap) ≫
            eqToHom (by
              change ModuleCat.of k (Module.Dual k ((K.X (-q + 3)).X (-p - 3))) =
                ModuleCat.of k
                  (Module.Dual k ((K.X (-(q + -3))).X (-(p + 3))))
              congr 3 <;> try rfl
              all_goals first | rfl | (congr 2 <;> ring)))
        (by
          intros p p' q _
          change (ModuleCat.ofHom (((period.inv.f (-q)).f (-p)).hom.dualMap) ≫
              eqToHom (dualPeriodIso_component_eq K p q)) ≫
              (((dualComplex K).bidegreeShift 3 (-3)).d p p').f q =
            ((dualComplex K).d p p').f q ≫
              (ModuleCat.ofHom (((period.inv.f (-q)).f (-p')).hom.dualMap) ≫
                eqToHom (dualPeriodIso_component_eq K p' q))
          have hs := dualPeriodIso_transport _ _
            (dualPeriodIso_component_eq K p q) (dualPeriodIso_component_eq K p' q)
            (dualPeriodIso_d₁ K p p' q)
          have hdual := dualPeriodIso_dualMap_square
            ((period.inv.f (-q)).f (-p')) ((K.X (-q)).d (-p') (-p))
            (((K.bidegreeShift 3 (-3)).X (-q)).d (-p') (-p))
            ((period.inv.f (-q)).f (-p)) ((period.inv.f (-q)).comm (-p') (-p))
          change _ = ModuleCat.ofHom (((K.X (-q)).d (-p') (-p)).hom.dualMap) ≫ _
          erw [Category.assoc, hs, ← Category.assoc, hdual]
          rfl)
        (by
          intros p q q' _
          change (ModuleCat.ofHom (((period.inv.f (-q)).f (-p)).hom.dualMap) ≫
              eqToHom (dualPeriodIso_component_eq K p q)) ≫
              (((dualComplex K).bidegreeShift 3 (-3)).X p).d q q' =
            ((dualComplex K).X p).d q q' ≫
              (ModuleCat.ofHom (((period.inv.f (-q')).f (-p)).hom.dualMap) ≫
                eqToHom (dualPeriodIso_component_eq K p q'))
          have hs := dualPeriodIso_transport _ _
            (dualPeriodIso_component_eq K p q) (dualPeriodIso_component_eq K p q')
            (dualPeriodIso_d₂ K p q q')
          have hdual := dualPeriodIso_dualMap_square
            ((period.inv.f (-q')).f (-p)) ((K.d (-q') (-q)).f (-p))
            (((K.bidegreeShift 3 (-3)).d (-q') (-q)).f (-p))
            ((period.inv.f (-q)).f (-p))
            (HomologicalComplex.congr_hom (period.inv.comm (-q') (-q)) (-p))
          change _ = ModuleCat.ofHom (((K.d (-q') (-q)).f (-p)).hom.dualMap) ≫ _
          erw [Category.assoc, hs, ← Category.assoc, hdual]
          rfl)
      inv := HomologicalComplex₂.homMk
        (fun ⟨p, q⟩ =>
          eqToHom (by
              change ModuleCat.of k
                  (Module.Dual k ((K.X (-(q + -3))).X (-(p + 3)))) =
                ModuleCat.of k (Module.Dual k ((K.X (-q + 3)).X (-p - 3)))
              congr 3 <;> try rfl
              all_goals first | rfl | (congr 2 <;> ring)) ≫
            ModuleCat.ofHom (((period.hom.f (-q)).f (-p)).hom.dualMap))
        (by
          intros p p' q _
          change (eqToHom (dualPeriodIso_component_eq K p q).symm ≫
              ModuleCat.ofHom (((period.hom.f (-q)).f (-p)).hom.dualMap) ≫
              ModuleCat.ofHom (((K.X (-q)).d (-p') (-p)).hom.dualMap)) =
            (((dualComplex K).bidegreeShift 3 (-3)).d p p').f q ≫
              (eqToHom (dualPeriodIso_component_eq K p' q).symm ≫
                ModuleCat.ofHom (((period.hom.f (-q)).f (-p')).hom.dualMap))
          have hcomm := (period.hom.f (-q)).comm (-p') (-p)
          have hdual := dualPeriodIso_dualMap_square
            ((period.hom.f (-q)).f (-p'))
            (((K.bidegreeShift 3 (-3)).X (-q)).d (-p') (-p))
            ((K.X (-q)).d (-p') (-p))
            ((period.hom.f (-q)).f (-p)) hcomm
          have hs := dualPeriodIso_transport _ _
            (dualPeriodIso_component_eq K p q).symm
            (dualPeriodIso_component_eq K p' q).symm
            (dualPeriodIso_d₁ K p p' q).symm
          erw [hdual, ← Category.assoc, hs]
          rfl)
        (by
          intros p q q' _
          change (eqToHom (dualPeriodIso_component_eq K p q).symm ≫
              ModuleCat.ofHom (((period.hom.f (-q)).f (-p)).hom.dualMap) ≫
              ModuleCat.ofHom (((K.d (-q') (-q)).f (-p)).hom.dualMap)) =
            (((dualComplex K).bidegreeShift 3 (-3)).X p).d q q' ≫
              (eqToHom (dualPeriodIso_component_eq K p q').symm ≫
                ModuleCat.ofHom (((period.hom.f (-q')).f (-p)).hom.dualMap))
          have hcomm := HomologicalComplex.congr_hom (period.hom.comm (-q') (-q)) (-p)
          have hdual := dualPeriodIso_dualMap_square
            ((period.hom.f (-q')).f (-p))
            (((K.bidegreeShift 3 (-3)).d (-q') (-q)).f (-p))
            ((K.d (-q') (-q)).f (-p))
            ((period.hom.f (-q)).f (-p)) hcomm
          have hs := dualPeriodIso_transport _ _
            (dualPeriodIso_component_eq K p q).symm
            (dualPeriodIso_component_eq K p q').symm
            (dualPeriodIso_d₂ K p q q').symm
          erw [hdual, ← Category.assoc, hs]
          rfl)
      hom_inv_id := by
        apply HomologicalComplex.hom_ext
        intro p
        apply HomologicalComplex.hom_ext
        intro q
        dsimp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
          HomologicalComplex₂.homMk, HomologicalComplex₂.toGradedObject]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        apply ModuleCat.hom_ext
        change (((period.hom.f (-q)).f (-p)).hom.dualMap.comp
          (((period.inv.f (-q)).f (-p)).hom.dualMap)) = LinearMap.id
        rw [LinearMap.dualMap_comp_dualMap, ← ModuleCat.hom_comp,
          ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, period.hom_inv_id]
        exact LinearMap.dualMap_id
      inv_hom_id := by
        apply HomologicalComplex.hom_ext
        intro p
        apply HomologicalComplex.hom_ext
        intro q
        have hi : ModuleCat.ofHom (((period.hom.f (-q)).f (-p)).hom.dualMap) ≫
            ModuleCat.ofHom (((period.inv.f (-q)).f (-p)).hom.dualMap) = 𝟙 _ := by
          apply ModuleCat.hom_ext
          change (((period.inv.f (-q)).f (-p)).hom.dualMap.comp
            (((period.hom.f (-q)).f (-p)).hom.dualMap)) = LinearMap.id
          rw [LinearMap.dualMap_comp_dualMap, ← ModuleCat.hom_comp,
            ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, period.inv_hom_id]
          exact LinearMap.dualMap_id
        dsimp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
          HomologicalComplex₂.homMk, HomologicalComplex₂.toGradedObject]
        erw [Category.assoc, ← Category.assoc _ _ (eqToHom _), hi]
        simp }
  exact (-1 : ℤˣ) • raw

/-- The oppositely indexed finite-dimensional dual of a matress is a matress. -/
theorem dualMatress (K : HomologicalComplex₂ (ModuleCat.{u} k) (up ℤ) (up ℤ))
    (period : K ≅ K.bidegreeShift 3 (-3))
    [∀ p q : ℤ, FiniteDimensional k ((K.X p).X q)]
    (hK : ModuleMatress K period) :
    ModuleMatress (dualComplex K) (dualPeriodIso K period) := sorry

end ModuleMatress

end HomologicalComplex₂

end
