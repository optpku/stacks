/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.RingHom.Local.Map
public import ReasLib.RingTheory.RingHom.Local.Residue

@[expose] public section

/-!
# Lifts from Henselizations

A henselization lifts canonically to every henselian local algebra over its base.
`liftFun` evaluates an element at an étale stage of the given ind-étale presentation,
using Henselian simple-root lifting in a standard étale neighbourhood. All choices
in this function use proved existence statements; the intrinsic owner remains a `Prop`.
`lift` bundles the resulting local algebra map, and `algEquiv` compares two henselizations
using these lifts in both directions.

@stack 04GS
-/

open IsLocalRing Polynomial CategoryTheory CategoryTheory.Limits

universe u v w x

namespace IsHenselizationOf.LiftConstruction

section ResidueUniqueness

variable {R : Type u} {A : Type v} {T : Type w}
variable [CommRing R] [CommRing A] [CommRing T]
variable [Algebra R A] [Algebra R T] [IsLocalRing T]

/-- A simple root of a polynomial in a local ring is determined by its residue. -/
theorem root_eq_of_residue_eq (p : T[X]) {a b : T}
    (ha : p.eval a = 0) (hb : p.eval b = 0)
    (hd : IsUnit (p.derivative.eval a)) (hr : residue T a = residue T b) : a = b := by
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr ha
  have hda : p.derivative.eval a = q.eval a := by
    rw [hq]
    simp
  rw [hda] at hd
  have hrq : residue T (q.eval b) = residue T (q.eval a) := by
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval₂_at_apply, hr]
  have hu : IsUnit (q.eval b) := (residue_ne_zero_iff_isUnit _).mp
    (hrq ▸ (residue_ne_zero_iff_isUnit _).mpr hd)
  have hz : (b - a) * q.eval b = 0 := by
    simpa [hq] using hb
  exact (sub_eq_zero.mp (hu.mul_left_eq_zero.mp hz)).symm

/-- Maps from a standard étale algebra to a local ring are determined by their residues. -/
theorem standard_hom_ext (P : StandardEtalePair R) (f g : P.Ring →ₐ[R] T)
    (h : ∀ a, residue T (f a) = residue T (g a)) : f = g := by
  apply P.hom_ext
  let Q := P.map (algebraMap R T)
  have hf : Q.HasMap (f P.X) := (P.hasMap_X.map f).map_algebraMap
  have hg : Q.HasMap (g P.X) := (P.hasMap_X.map g).map_algebraMap
  exact root_eq_of_residue_eq Q.f
    (by simpa [Polynomial.aeval_def] using hf.1)
    (by simpa [Polynomial.aeval_def] using hg.1)
    (by simpa [Polynomial.aeval_def] using hf.isUnit_derivative_f) (h P.X)

/-- Maps from an étale algebra to a local ring are determined by their residues. -/
theorem etale_hom_ext [Algebra.Etale R A] (f g : A →ₐ[R] T)
    (h : ∀ a, residue T (f a) = residue T (g a)) : f = g := by
  let q := RingHom.ker ((residue T).comp f.toRingHom)
  haveI : q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨s, hs, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) q
  letI : Algebra.IsStandardEtale R (Localization.Away s) := hstd
  have hf : IsUnit (f s) := (residue_ne_zero_iff_isUnit _).mp hs
  have hg : IsUnit (g s) := (residue_ne_zero_iff_isUnit _).mp (h s ▸ hs)
  let fs : Localization.Away s →ₐ[R] T := IsLocalization.Away.liftAlgHom s hf (f := f)
  let gs : Localization.Away s →ₐ[R] T := IsLocalization.Away.liftAlgHom s hg (f := g)
  have hres : (residue T).comp fs.toRingHom = (residue T).comp gs.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext a
    simpa [fs, gs, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq] using h a
  let P : StandardEtalePresentation R (Localization.Away s) :=
    Classical.choice Algebra.IsStandardEtale.nonempty_standardEtalePresentation
  have he : fs.comp P.equivRing.symm.toAlgHom = gs.comp P.equivRing.symm.toAlgHom :=
    standard_hom_ext P.P _ _ (fun a => DFunLike.congr_fun hres (P.equivRing.symm a))
  have he' : fs = gs := by
    apply AlgHom.ext
    intro a
    simpa using AlgHom.congr_fun he (P.equivRing a)
  ext a
  have hh := AlgHom.congr_fun he' (algebraMap A (Localization.Away s) a)
  simpa [fs, gs, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq] using hh


end ResidueUniqueness

/- The implementation records exactly the presentation supplied by `IndEtale`.
No lift or comparison is selected from a deferred existence theorem. -/

variable {R : Type u} {A : Type v} {T : Type w}
variable [CommRing R] [CommRing A] [CommRing T] [Algebra R A] [Algebra R T]
variable [HenselianLocalRing T]

/-- A standard étale residue point lifts to a root with the prescribed residue. -/
theorem standard_exists_root (P : StandardEtalePair R)
    (τ : P.Ring →ₐ[R] ResidueField T) :
    ∃ a : T, P.HasMap a ∧ residue T a = τ P.X := by
  let Q := P.map (algebraMap R T)
  have hκ : Q.HasMap (τ P.X) := (P.hasMap_X.map τ).map_algebraMap
  have hd : aeval (τ P.X) Q.f.derivative ≠ 0 :=
    isUnit_iff_ne_zero.mp hκ.isUnit_derivative_f
  obtain ⟨a, ha, hres⟩ := ((HenselianLocalRing.TFAE T).out 0 1 rfl rfl).mp
    (inferInstance : HenselianLocalRing T) Q.f Q.monic_f (τ P.X) hκ.1 hd
  refine ⟨a, ⟨?_, ?_⟩, hres⟩
  · simpa [Q, StandardEtalePair.map, Polynomial.IsRoot, Polynomial.aeval_def] using ha
  · apply (residue_ne_zero_iff_isUnit _).mp
    have hg : aeval (τ P.X) Q.g ≠ 0 := isUnit_iff_ne_zero.mp hκ.2
    have hEval := Polynomial.aeval_algHom_apply
      (Ideal.Quotient.mkₐ T (maximalIdeal T)) a Q.g
    have hg' : residue T (aeval (R := T) a Q.g) ≠ 0 := by
      change (Ideal.Quotient.mkₐ T (maximalIdeal T)) (aeval a Q.g) ≠ 0
      rw [← hEval]
      change aeval (residue T a) Q.g ≠ 0
      rw [hres]
      exact hg
    simpa [Q, StandardEtalePair.map, Polynomial.aeval_def] using hg'

/-- Evaluate a standard étale algebra at the lifted simple root. -/
noncomputable def standardLift (P : StandardEtalePair R)
    (τ : P.Ring →ₐ[R] ResidueField T) : P.Ring →ₐ[R] T :=
  P.lift (standard_exists_root P τ).choose (standard_exists_root P τ).choose_spec.1

/-- Lift an étale residue point through a standard étale neighbourhood of its kernel. -/
noncomputable def etaleLift [Algebra.Etale R A]
    (τ : A →ₐ[R] ResidueField T) : A →ₐ[R] T := by
  let q := RingHom.ker τ.toRingHom
  haveI : q.IsPrime := RingHom.ker_isPrime τ.toRingHom
  let h := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) q
  let g : A := h.choose
  have hg : τ g ≠ 0 := h.choose_spec.1
  letI : Algebra.IsStandardEtale R (Localization.Away g) := h.choose_spec.2
  let P : StandardEtalePresentation R (Localization.Away g) :=
    Classical.choice Algebra.IsStandardEtale.nonempty_standardEtalePresentation
  let τg : Localization.Away g →ₐ[R] ResidueField T :=
    IsLocalization.Away.liftAlgHom g (isUnit_iff_ne_zero.mpr hg) (f := τ)
  exact ((standardLift P.P (τg.comp P.equivRing.symm.toAlgHom)).comp
    P.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom R A (Localization.Away g))

/-- The standard étale lift induces its prescribed residue point on every element. -/
theorem standardLift_residue (P : StandardEtalePair R)
    (τ : P.Ring →ₐ[R] ResidueField T) (a : P.Ring) :
    residue T (standardLift P τ a) = τ a := by
  have he : (IsScalarTower.toAlgHom R T (ResidueField T)).comp (standardLift P τ) = τ := by
    apply P.hom_ext
    change residue T (standardLift P τ P.X) = τ P.X
    rw [standardLift, P.lift_X]
    exact (standard_exists_root P τ).choose_spec.2
  exact AlgHom.congr_fun he a

/-- The étale lift induces its prescribed residue point on every element. -/
theorem etaleLift_residue [Algebra.Etale R A]
    (τ : A →ₐ[R] ResidueField T) (a : A) : residue T (etaleLift τ a) = τ a := by
  dsimp only [etaleLift, AlgHom.comp_apply]
  rw [standardLift_residue]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
  simp only [IsScalarTower.toAlgHom_apply, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

section Presentation

/-- The complete filtered étale presentation supplied by the ind-étale hypothesis. -/
structure Presentation {X Y : CommRingCat.{u}} (f : X ⟶ Y) where
  index : Type u
  [category : SmallCategory index]
  [filtered : IsFiltered index]
  diagram : index ⥤ CommRingCat.{u}
  base : (Functor.const index).obj X ⟶ diagram
  cocone : diagram ⟶ (Functor.const index).obj Y
  isColimit : IsColimit (Cocone.mk Y cocone)
  spec : ∀ j, CommRingCat.etale (base.app j) ∧ base.app j ≫ cocone.app j = f

/-- Reify the given ind-étale witness, including its actual colimit data. -/
noncomputable def presentation {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (h : CategoryTheory.MorphismProperty.ind.{u} CommRingCat.etale f) : Presentation f :=
  Classical.choice (show Nonempty (Presentation f) from by
    obtain ⟨J, cat, filtered, D, t, s, hc, ht⟩ := h
    exact ⟨{
      index := J
      category := cat
      filtered := filtered
      diagram := D
      base := t
      cocone := s
      isColimit := hc
      spec := ht }⟩)

/-- Every element has a representative at an actual stage of the presentation. -/
theorem presentation_exists_rep {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) (a : Y) :
    letI := P.category
    ∃ z : Σ j : P.index, P.diagram.obj j, (P.cocone.app z.1).hom z.2 = a := by
  letI := P.category
  letI := P.filtered
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget CommRingCat.{u}) P.isColimit) a
  exact ⟨⟨j, x⟩, hx⟩

/-- Choose a stage element whose colimit image is exactly the given element. -/
noncomputable def presentationRep {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) (a : Y) :
    letI := P.category
    Σ j : P.index, P.diagram.obj j :=
  (presentation_exists_rep P a).choose

/-- The selected representative has the required image. -/
theorem presentationRep_spec {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) (a : Y) :
    letI := P.category
    (P.cocone.app (presentationRep P a).1).hom (presentationRep P a).2 = a :=
  (presentation_exists_rep P a).choose_spec

/-- Lift the residue point restricted to a single étale stage. -/
noncomputable def presentationStageAlgLift {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (τ : Y →+* ResidueField T)
    (hτ : τ.comp f.hom = (residue T).comp (algebraMap X T)) (j : P.index) :
    letI := P.category
    letI : Algebra X (P.diagram.obj j) := (P.base.app j).hom.toAlgebra
    P.diagram.obj j →ₐ[X] T := by
  letI := P.category
  letI : Algebra X (P.diagram.obj j) := (P.base.app j).hom.toAlgebra
  letI : Algebra.Etale X (P.diagram.obj j) := (P.spec j).1
  let τj : P.diagram.obj j →ₐ[X] ResidueField T :=
    { toRingHom := τ.comp (P.cocone.app j).hom
      commutes' := fun r => by
        have hc : (P.cocone.app j).hom ((P.base.app j).hom r) = f.hom r :=
          congrArg (fun q : X ⟶ Y => q.hom r) (P.spec j).2
        change τ ((P.cocone.app j).hom ((P.base.app j).hom r)) = _
        rw [hc]
        exact DFunLike.congr_fun hτ r }
  exact etaleLift (R := X) (A := P.diagram.obj j) τj

/-- The ring map underlying the stage algebra lift. -/
noncomputable def presentationStageLift {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (τ : Y →+* ResidueField T)
    (hτ : τ.comp f.hom = (residue T).comp (algebraMap X T)) (j : P.index) :
    (letI := P.category; P.diagram.obj j) →+* T :=
  letI := P.category
  letI : Algebra X (P.diagram.obj j) := (P.base.app j).hom.toAlgebra
  (presentationStageAlgLift P τ hτ j).toRingHom

/-- Each stage map is a map over the base. -/
theorem presentationStageLift_commutes {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (τ : Y →+* ResidueField T)
    (hτ : τ.comp f.hom = (residue T).comp (algebraMap X T)) (j : P.index) (r : X) :
    letI := P.category
    presentationStageLift P τ hτ j ((P.base.app j).hom r) = algebraMap X T r :=
  letI := P.category
  letI : Algebra X (P.diagram.obj j) := (P.base.app j).hom.toAlgebra
  (presentationStageAlgLift P τ hτ j).commutes r

/-- Each stage lift has its prescribed residue. -/
theorem presentationStageLift_residue {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (τ : Y →+* ResidueField T)
    (hτ : τ.comp f.hom = (residue T).comp (algebraMap X T)) (j : P.index) :
    letI := P.category
    ∀ a : P.diagram.obj j,
      residue T (presentationStageLift P τ hτ j a) = τ ((P.cocone.app j).hom a) := by
  letI := P.category
  intro a
  letI : Algebra X (P.diagram.obj j) := (P.base.app j).hom.toAlgebra
  letI : Algebra.Etale X (P.diagram.obj j) := (P.spec j).1
  unfold presentationStageLift presentationStageAlgLift
  exact etaleLift_residue (R := X) _ _

/-- Uniqueness of étale residue lifts makes the stage maps compatible with transitions. -/
theorem presentationStageLift_naturality {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (τ : Y →+* ResidueField T)
    (hτ : τ.comp f.hom = (residue T).comp (algebraMap X T)) :
    letI := P.category
    ∀ {i j : P.index} (s : i ⟶ j) (a : P.diagram.obj i),
      presentationStageLift P τ hτ j ((P.diagram.map s).hom a) =
        presentationStageLift P τ hτ i a := by
  letI := P.category
  intro i j s a
  letI : Algebra X (P.diagram.obj i) := (P.base.app i).hom.toAlgebra
  letI : Algebra.Etale X (P.diagram.obj i) := (P.spec i).1
  let left : P.diagram.obj i →ₐ[X] T :=
    { toRingHom := (presentationStageLift P τ hτ j).comp (P.diagram.map s).hom
      commutes' := fun r => by
        have hb : (P.diagram.map s).hom ((P.base.app i).hom r) =
            (P.base.app j).hom r :=
          (congrArg (fun q : X ⟶ P.diagram.obj j => q.hom r) (P.base.naturality s)).symm
        change presentationStageLift P τ hτ j ((P.diagram.map s).hom ((P.base.app i).hom r)) = _
        rw [hb]
        exact presentationStageLift_commutes P τ hτ j r }
  have he : left = presentationStageAlgLift P τ hτ i := by
    apply etale_hom_ext
    intro b
    change residue T (presentationStageLift P τ hτ j ((P.diagram.map s).hom b)) =
      residue T (presentationStageLift P τ hτ i b)
    rw [presentationStageLift_residue, presentationStageLift_residue]
    exact congrArg τ (congrArg (fun q : P.diagram.obj i ⟶ Y => q.hom b)
      (P.cocone.naturality s))
  exact AlgHom.congr_fun he a

/-- Equal colimit images give the same lifted value, independently of their representatives. -/
theorem presentationStageLift_eq_of_cocone_eq {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (τ : Y →+* ResidueField T)
    (hτ : τ.comp f.hom = (residue T).comp (algebraMap X T)) :
    letI := P.category
    ∀ (i j : P.index) (a : P.diagram.obj i) (b : P.diagram.obj j),
      (P.cocone.app i).hom a = (P.cocone.app j).hom b →
      presentationStageLift P τ hτ i a = presentationStageLift P τ hτ j b := by
  letI := P.category
  letI := P.filtered
  intro i j a b h
  obtain ⟨k, si, sj, hij⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff (P.diagram ⋙ forget CommRingCat.{u})
      (isColimitOfPreserves (forget CommRingCat.{u}) P.isColimit)).mp h
  calc
    presentationStageLift P τ hτ i a =
        presentationStageLift P τ hτ k ((P.diagram.map si).hom a) :=
      (presentationStageLift_naturality P τ hτ si a).symm
    _ = presentationStageLift P τ hτ k ((P.diagram.map sj).hom b) :=
      congrArg (presentationStageLift P τ hτ k) hij
    _ = presentationStageLift P τ hτ j b := presentationStageLift_naturality P τ hτ sj b

/-- Evaluate a colimit representative using its stage lift, for any target universe. -/
noncomputable def presentationFun {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (τ : Y →+* ResidueField T)
    (hτ : τ.comp f.hom = (residue T).comp (algebraMap X T)) (a : Y) : T :=
  let z := presentationRep P a
  presentationStageLift P τ hτ z.1 z.2

/-- The induced function agrees with every stage lift, for every representative. -/
theorem presentationFun_cocone {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (τ : Y →+* ResidueField T)
    (hτ : τ.comp f.hom = (residue T).comp (algebraMap X T)) (j : P.index) :
    letI := P.category
    ∀ a : P.diagram.obj j,
      presentationFun P τ hτ ((P.cocone.app j).hom a) = presentationStageLift P τ hτ j a := by
  letI := P.category
  intro a
  exact presentationStageLift_eq_of_cocone_eq P τ hτ _ _ _ _
    (presentationRep_spec P ((P.cocone.app j).hom a))

set_option backward.isDefEq.respectTransparency false in
/-- The colimit lift preserves one. -/
theorem presentationFun_one {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (τ : Y →+* ResidueField T)
    (hτ : τ.comp f.hom = (residue T).comp (algebraMap X T)) :
    presentationFun P τ hτ 1 = 1 := by
  letI := P.category
  letI := P.filtered
  let j : P.index := Classical.choice IsFiltered.nonempty
  simpa only [map_one] using presentationFun_cocone P τ hτ j 1

set_option backward.isDefEq.respectTransparency false in
/-- The colimit lift preserves zero. -/
theorem presentationFun_zero {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (τ : Y →+* ResidueField T)
    (hτ : τ.comp f.hom = (residue T).comp (algebraMap X T)) :
    presentationFun P τ hτ 0 = 0 := by
  letI := P.category
  letI := P.filtered
  let j : P.index := Classical.choice IsFiltered.nonempty
  simpa only [map_zero] using presentationFun_cocone P τ hτ j 0

set_option backward.isDefEq.respectTransparency false in
/-- Two elements can be computed at a common stage, so the lift preserves addition. -/
theorem presentationFun_add {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (τ : Y →+* ResidueField T)
    (hτ : τ.comp f.hom = (residue T).comp (algebraMap X T)) (a b : Y) :
    presentationFun P τ hτ (a + b) = presentationFun P τ hτ a + presentationFun P τ hτ b := by
  letI := P.category
  letI := P.filtered
  obtain ⟨j, x, y, rfl, rfl⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves (forget CommRingCat.{u}) P.isColimit) a b
  change presentationFun P τ hτ ((P.cocone.app j).hom x + (P.cocone.app j).hom y) =
    presentationFun P τ hτ ((P.cocone.app j).hom x) + presentationFun P τ hτ ((P.cocone.app j).hom y)
  rw [← map_add, presentationFun_cocone, presentationFun_cocone, presentationFun_cocone]
  exact map_add _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Computing a product at a common stage proves multiplicativity. -/
theorem presentationFun_mul {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (τ : Y →+* ResidueField T)
    (hτ : τ.comp f.hom = (residue T).comp (algebraMap X T)) (a b : Y) :
    presentationFun P τ hτ (a * b) = presentationFun P τ hτ a * presentationFun P τ hτ b := by
  letI := P.category
  letI := P.filtered
  obtain ⟨j, x, y, rfl, rfl⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂
    (isColimitOfPreserves (forget CommRingCat.{u}) P.isColimit) a b
  change presentationFun P τ hτ ((P.cocone.app j).hom x * (P.cocone.app j).hom y) =
    presentationFun P τ hτ ((P.cocone.app j).hom x) * presentationFun P τ hτ ((P.cocone.app j).hom y)
  rw [← map_mul, presentationFun_cocone, presentationFun_cocone, presentationFun_cocone]
  exact map_mul _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The induced map commutes with the given base map. -/
theorem presentationFun_base {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (τ : Y →+* ResidueField T)
    (hτ : τ.comp f.hom = (residue T).comp (algebraMap X T)) (r : X) :
    presentationFun P τ hτ (f.hom r) = algebraMap X T r := by
  letI := P.category
  letI := P.filtered
  let j : P.index := Classical.choice IsFiltered.nonempty
  have he := congrArg (fun q : X ⟶ Y => q.hom r) (P.spec j).2
  change (P.cocone.app j).hom ((P.base.app j).hom r) = f.hom r at he
  rw [← he, presentationFun_cocone]
  exact presentationStageLift_commutes P τ hτ j r

set_option backward.isDefEq.respectTransparency false in
/-- The induced map lifts the original residue point. -/
theorem presentationFun_residue {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (τ : Y →+* ResidueField T)
    (hτ : τ.comp f.hom = (residue T).comp (algebraMap X T)) (a : Y) :
    residue T (presentationFun P τ hτ a) = τ a := by
  letI := P.category
  obtain ⟨⟨j, x⟩, rfl⟩ := presentation_exists_rep P a
  rw [presentationFun_cocone, presentationStageLift_residue]

/-- Restrict a map over the base to a single stage of the presentation. -/
noncomputable def presentationRestrict {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (g : Y →+* T)
    (hg : g.comp f.hom = algebraMap X T) (j : P.index) :
    letI := P.category
    letI : Algebra X (P.diagram.obj j) := (P.base.app j).hom.toAlgebra
    P.diagram.obj j →ₐ[X] T := by
  letI := P.category
  letI : Algebra X (P.diagram.obj j) := (P.base.app j).hom.toAlgebra
  exact
    { toRingHom := g.comp (P.cocone.app j).hom
      commutes' := fun r => by
        have he := congrArg (fun q : X ⟶ Y => q.hom r) (P.spec j).2
        change (P.cocone.app j).hom ((P.base.app j).hom r) = f.hom r at he
        change g ((P.cocone.app j).hom ((P.base.app j).hom r)) = _
        rw [he]
        exact DFunLike.congr_fun hg r }

/-- Maps from the ind-étale colimit to a local ring are determined by their residue maps. -/
theorem presentation_hom_ext {X Y : CommRingCat.{u}} {f : X ⟶ Y}
    (P : Presentation f) [Algebra X T] (g₁ g₂ : Y →+* T)
    (h₁ : g₁.comp f.hom = algebraMap X T) (h₂ : g₂.comp f.hom = algebraMap X T)
    (hres : ∀ a, residue T (g₁ a) = residue T (g₂ a)) : g₁ = g₂ := by
  letI := P.category
  apply RingHom.ext
  intro a
  obtain ⟨⟨j, x⟩, rfl⟩ := presentation_exists_rep P a
  letI : Algebra X (P.diagram.obj j) := (P.base.app j).hom.toAlgebra
  letI : Algebra.Etale X (P.diagram.obj j) := (P.spec j).1
  have he : presentationRestrict P g₁ h₁ j = presentationRestrict P g₂ h₂ j :=
    etale_hom_ext (R := X) _ _ (fun b => hres ((P.cocone.app j).hom b))
  exact AlgHom.congr_fun he x

end Presentation

end IsHenselizationOf.LiftConstruction

namespace IsHenselizationOf

section ResidueLift

variable {R : Type u} {Rh : Type v} {T : Type w}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing T] [IsLocalRing T] [Algebra R T]
variable [IsLocalHom (algebraMap R T)]

/-- The residue point of a henselization forced by the local structural map to `T`. -/
noncomputable def residueLift : Rh →ₐ[R] ResidueField T where
  toRingHom := (ResidueField.map (algebraMap R T)).comp
    ((IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm.toRingHom.comp
      (residue Rh))
  commutes' r := by
    change (ResidueField.map (algebraMap R T))
      ((IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm
        (residue Rh (algebraMap R Rh r))) = _
    change (ResidueField.map (algebraMap R T))
      ((IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm
        ((IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)) (residue R r))) = _
    rw [RingEquiv.symm_apply_apply]
    rfl

/-- The residue point extends the structural map from the base. -/
@[simp]
theorem residueLift_apply_algebraMap (r : R) :
    residueLift (R := R) (Rh := Rh) (T := T) (algebraMap R Rh r) =
      algebraMap R (ResidueField T) r :=
  (residueLift (R := R) (Rh := Rh) (T := T)).commutes r

end ResidueLift

section Lift

variable {R : Type u} {Rh : Type v} {T : Type w}
variable [hCommR : CommRing R] [hLocalR : IsLocalRing R]
variable [hCommRh : CommRing Rh] [hRRh : Algebra R Rh] [hRh : IsHenselizationOf R Rh]
variable [hCommT : CommRing T] [hT : HenselianLocalRing T] [hRT : Algebra R T]
variable [hRTLocal : IsLocalHom (algebraMap R T)]

include hCommR hLocalR hCommRh hRRh hRh hCommT hT hRT hRTLocal

/-- The function underlying the canonical lift. An element is represented at a genuine
étale stage, where its image is obtained by Henselian lifting of the prescribed residue root.
The target universe is independent of both the base and the henselization. -/
noncomputable def liftFun (x : Rh) : T := by
  let f := CommRingCat.ofHom (algebraMap R Rh).ulift.{v, u}
  let P := LiftConstruction.presentation
    (show CategoryTheory.MorphismProperty.ind.{max u v} CommRingCat.etale f from
      IsHenselizationOf.isFilteredColimitOfEtale (R := R) (S := Rh))
  letI : Algebra (ULift.{v} R) T :=
    ((algebraMap R T).comp (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom).toAlgebra
  let τ : ULift.{u} Rh →+* ResidueField T :=
    (residueLift (R := R) (Rh := Rh) (T := T)).toRingHom.comp
      (ULift.ringEquiv : ULift.{u} Rh ≃+* Rh).toRingHom
  have hτ : τ.comp f.hom = (residue T).comp (algebraMap (ULift.{v} R) T) := by
    ext r
    exact (residueLift (R := R) (Rh := Rh) (T := T)).commutes r.down
  exact LiftConstruction.presentationFun P τ hτ (ULift.up x)

theorem liftFun_one : liftFun (R := R) (Rh := Rh) (T := T) 1 = 1 := by
  letI : Algebra (ULift.{v} R) T :=
    ((algebraMap R T).comp (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom).toAlgebra
  unfold liftFun
  exact LiftConstruction.presentationFun_one _ _ _

theorem liftFun_zero : liftFun (R := R) (Rh := Rh) (T := T) 0 = 0 := by
  letI : Algebra (ULift.{v} R) T :=
    ((algebraMap R T).comp (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom).toAlgebra
  unfold liftFun
  exact LiftConstruction.presentationFun_zero _ _ _

theorem liftFun_mul (a b : Rh) :
    liftFun (R := R) (T := T) (a * b) =
      liftFun (R := R) (T := T) a * liftFun (R := R) (T := T) b := by
  letI : Algebra (ULift.{v} R) T :=
    ((algebraMap R T).comp (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom).toAlgebra
  unfold liftFun
  exact LiftConstruction.presentationFun_mul _ _ _ _ _

theorem liftFun_add (a b : Rh) :
    liftFun (R := R) (T := T) (a + b) =
      liftFun (R := R) (T := T) a + liftFun (R := R) (T := T) b := by
  letI : Algebra (ULift.{v} R) T :=
    ((algebraMap R T).comp (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom).toAlgebra
  unfold liftFun
  exact LiftConstruction.presentationFun_add _ _ _ _ _

theorem liftFun_algebraMap (r : R) :
    liftFun (R := R) (Rh := Rh) (T := T) (algebraMap R Rh r) = algebraMap R T r := by
  letI : Algebra (ULift.{v} R) T :=
    ((algebraMap R T).comp (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom).toAlgebra
  unfold liftFun
  exact LiftConstruction.presentationFun_base
    (f := CommRingCat.ofHom (algebraMap R Rh).ulift.{v, u}) _ _ _ (ULift.up r)

/-- The lift induces the prescribed residue point. -/
theorem liftFun_residue (a : Rh) :
    residue T (liftFun (R := R) (T := T) a) =
      residueLift (R := R) (Rh := Rh) (T := T) a := by
  letI : Algebra (ULift.{v} R) T :=
    ((algebraMap R T).comp (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom).toAlgebra
  unfold liftFun
  exact LiftConstruction.presentationFun_residue _ _ _ _

/-- The algebra homomorphism with the explicitly constructed lift function. -/
noncomputable def liftHom : Rh →ₐ[R] T where
  toFun := liftFun (R := R) (Rh := Rh) (T := T)
  map_one' := liftFun_one
  map_zero' := liftFun_zero
  map_mul' := liftFun_mul
  map_add' := liftFun_add
  commutes' := liftFun_algebraMap

/-- The constructed lift reflects units, as its residue map does. -/
theorem liftHom_isLocalHom : IsLocalHom (liftHom (R := R) (Rh := Rh) (T := T)).toRingHom := by
  refine ⟨fun a ha => ?_⟩
  apply (residue_ne_zero_iff_isUnit a).mp
  intro hzero
  have hne := (residue_ne_zero_iff_isUnit (liftHom (R := R) (T := T) a)).mpr ha
  apply hne
  change residue T (liftFun (R := R) (T := T) a) = 0
  rw [liftFun_residue]
  change (ResidueField.map (algebraMap R T))
    ((residueFieldEquiv (R := R) (S := Rh)).symm (residue Rh a)) = 0
  rw [hzero, map_zero, map_zero]

/-- Tag 04GS: the canonical local lift from a henselization to a henselian local target. -/
@[stacks 04GS "canonical local henselization lift"]
noncomputable def lift : AlgHom.Local (R := R) (A := Rh) (B := T) where
  hom := liftHom
  isLocal := liftHom_isLocalHom

/-- The underlying function of the bundled lift is `liftFun`. -/
@[simp]
theorem lift_hom_apply (a : Rh) :
    (lift (R := R) (Rh := Rh) (T := T)).hom a = liftFun (R := R) (T := T) a := rfl

/-- The lift commutes with the structural maps from the base. -/
@[simp]
theorem lift_apply_algebraMap (r : R) :
    (lift (R := R) (Rh := Rh) (T := T)).hom (algebraMap R Rh r) = algebraMap R T r :=
  (lift (R := R) (Rh := Rh) (T := T)).hom.commutes r

/-- The residue square of the canonical lift. -/
theorem lift_comp_residue :
    (residue T).comp (lift (R := R) (Rh := Rh) (T := T)).hom.toRingHom =
      (residueLift (R := R) (Rh := Rh) (T := T)).toRingHom :=
  RingHom.ext (liftFun_residue (R := R) (Rh := Rh) (T := T))

/-- The residue-field map of the lift is the base residue map transported through the
henselization's residue-field equivalence. -/
theorem lift_residueFieldMap :
    (lift (R := R) (Rh := Rh) (T := T)).residueFieldMap =
      (ResidueField.map (algebraMap R T)).comp
        (residueFieldEquiv (R := R) (S := Rh)).symm.toRingHom := by
  ext a
  obtain ⟨r, rfl⟩ := residue_surjective (R := Rh) a
  exact liftFun_residue (R := R) (Rh := Rh) (T := T) r

/-- Tag 04GS: two local lifts from a henselization to the same henselian local target
are equal. -/
@[ext, stacks 04GS "equality of henselization lifts"]
theorem local_eq (f g : AlgHom.Local (R := R) (A := Rh) (B := T)) : f = g := by
  letI : IsLocalHom f.hom.toRingHom := f.isLocal
  letI : IsLocalHom g.hom.toRingHom := g.isLocal
  have hres (a : Rh) : residue T (f.hom a) = residue T (g.hom a) := by
    obtain ⟨rκ, hrκ⟩ :=
      (IsHenselizationOf.residueField_bijective (R := R) (S := Rh)).surjective (residue Rh a)
    obtain ⟨r, rfl⟩ := residue_surjective (R := R) rκ
    have hr : residue Rh (algebraMap R Rh r) = residue Rh a := hrκ
    have hf := congrArg (ResidueField.map f.hom.toRingHom) hr
    have hg := congrArg (ResidueField.map g.hom.toRingHom) hr
    change residue T (f.hom (algebraMap R Rh r)) = residue T (f.hom a) at hf
    change residue T (g.hom (algebraMap R Rh r)) = residue T (g.hom a) at hg
    rw [f.hom.commutes] at hf
    rw [g.hom.commutes] at hg
    exact hf.symm.trans hg
  let φ := CommRingCat.ofHom (algebraMap R Rh).ulift.{v, u}
  let P := LiftConstruction.presentation
    (show CategoryTheory.MorphismProperty.ind.{max u v} CommRingCat.etale φ from
      IsHenselizationOf.isFilteredColimitOfEtale (R := R) (S := Rh))
  letI : Algebra (ULift.{v} R) T :=
    ((algebraMap R T).comp (ULift.ringEquiv : ULift.{v} R ≃+* R).toRingHom).toAlgebra
  let f' : ULift.{u} Rh →+* T :=
    f.hom.toRingHom.comp (ULift.ringEquiv : ULift.{u} Rh ≃+* Rh).toRingHom
  let g' : ULift.{u} Rh →+* T :=
    g.hom.toRingHom.comp (ULift.ringEquiv : ULift.{u} Rh ≃+* Rh).toRingHom
  have hf' : f'.comp φ.hom = algebraMap (ULift.{v} R) T := by
    ext r
    exact f.hom.commutes r.down
  have hg' : g'.comp φ.hom = algebraMap (ULift.{v} R) T := by
    ext r
    exact g.hom.commutes r.down
  have he := LiftConstruction.presentation_hom_ext P f' g' hf' hg' (fun a => hres a.down)
  have he' : f.hom = g.hom := AlgHom.ext fun a => DFunLike.congr_fun he (ULift.up a)
  cases f
  cases g
  cases he'
  rfl

/-- Tag 04GS: a henselization has a unique local lift to every henselian local algebra. -/
@[stacks 04GS "henselization universal property"]
theorem existsUnique_lift :
    ∃! f : Rh →ₐ[R] T, IsLocalHom f.toRingHom := by
  refine ⟨(lift (R := R) (Rh := Rh) (T := T)).hom,
    (lift (R := R) (Rh := Rh) (T := T)).isLocal, ?_⟩
  intro f hf
  exact congrArg AlgHom.Local.hom
    (local_eq ⟨f, hf⟩ (lift (R := R) (Rh := Rh) (T := T)))

/-- The canonical lift supplies the local-map existence statement. -/
@[stacks 04GS "existence of a local henselization lift"]
theorem local_nonempty :
    Nonempty (AlgHom.Local (R := R) (A := Rh) (B := T)) := ⟨lift⟩

/-- Local lifts to a fixed henselian local target form a subsingleton. -/
@[stacks 04GS "uniqueness of henselization lifts"]
theorem local_subsingleton :
    Subsingleton (AlgHom.Local (R := R) (A := Rh) (B := T)) := ⟨local_eq⟩

/-- Every local lift equals the constructed one. -/
theorem lift_unique (f : AlgHom.Local (R := R) (A := Rh) (B := T)) :
    f = lift (R := R) (Rh := Rh) (T := T) := local_eq f lift

/-- Postcomposition with a local map of henselian targets commutes with lifting. -/
theorem lift_naturality {U : Type x} [CommRing U] [HenselianLocalRing U]
    [Algebra R U] [IsLocalHom (algebraMap R U)]
    (f : AlgHom.Local (R := R) (A := T) (B := U)) :
    f.hom.comp (lift (R := R) (Rh := Rh) (T := T)).hom =
      (lift (R := R) (Rh := Rh) (T := U)).hom := by
  letI : IsLocalHom f.hom.toRingHom := f.isLocal
  letI : IsLocalHom (lift (R := R) (Rh := Rh) (T := T)).hom.toRingHom :=
    (lift (R := R) (Rh := Rh) (T := T)).isLocal
  exact congrArg AlgHom.Local.hom
    (local_eq ⟨f.hom.comp (lift (R := R) (Rh := Rh) (T := T)).hom, by
      change IsLocalHom (f.hom.toRingHom.comp (lift (R := R) (Rh := Rh) (T := T)).hom.toRingHom)
      infer_instance⟩ (lift (R := R) (Rh := Rh) (T := U)))

omit hCommR hLocalR hCommRh hRRh hRh hCommT hT hRT hRTLocal

end Lift

section Equiv

variable {R : Type u} {Rh : Type v} {Sh : Type w}
variable [hCommR : CommRing R] [hLocalR : IsLocalRing R]
variable [hCommRh : CommRing Rh] [hRRh : Algebra R Rh] [hRh : IsHenselizationOf R Rh]
variable [hCommSh : CommRing Sh] [hRSh : Algebra R Sh] [hSh : IsHenselizationOf R Sh]

include hCommR hLocalR hCommRh hRRh hRh hCommSh hRSh hSh

/-- Tag 04GS: explicit local lifts in both directions between two chosen
henselizations are mutually inverse, by uniqueness of local lifts into a
henselization.  The forward and inverse maps are the given lifts. -/
@[stacks 04GS "equivalence of henselizations from explicit local lifts"]
def algEquivOfLocal
    (f : AlgHom.Local (R := R) (A := Rh) (B := Sh))
    (g : AlgHom.Local (R := R) (A := Sh) (B := Rh)) : Rh ≃ₐ[R] Sh := by
  letI : IsLocalHom f.hom.toRingHom := f.isLocal
  letI : IsLocalHom g.hom.toRingHom := g.isLocal
  exact AlgEquiv.ofAlgHom f.hom g.hom
    (congrArg AlgHom.Local.hom
      (local_eq (R := R) (Rh := Sh) (T := Sh)
        ⟨f.hom.comp g.hom, by
          change IsLocalHom (f.hom.toRingHom.comp g.hom.toRingHom)
          infer_instance⟩
        ⟨AlgHom.id R Sh, by change IsLocalHom (RingHom.id Sh); infer_instance⟩))
    (congrArg AlgHom.Local.hom
      (local_eq (R := R) (Rh := Rh) (T := Rh)
        ⟨g.hom.comp f.hom, by
          change IsLocalHom (g.hom.toRingHom.comp f.hom.toRingHom)
          infer_instance⟩
        ⟨AlgHom.id R Rh, by change IsLocalHom (RingHom.id Rh); infer_instance⟩))

/-- The comparison built from explicit local lifts acts by the forward lift. -/
@[simp]
theorem algEquivOfLocal_apply
    (f : AlgHom.Local (R := R) (A := Rh) (B := Sh))
    (g : AlgHom.Local (R := R) (A := Sh) (B := Rh)) (x : Rh) :
    algEquivOfLocal f g x = f.hom x := rfl

/-- The inverse of the comparison built from explicit local lifts is the
backward lift. -/
@[simp]
theorem algEquivOfLocal_symm_apply
    (f : AlgHom.Local (R := R) (A := Rh) (B := Sh))
    (g : AlgHom.Local (R := R) (A := Sh) (B := Rh)) (y : Sh) :
    (algEquivOfLocal f g).symm y = g.hom y := rfl

/-- The canonical comparison of two henselizations, with the canonical lifts as its
forward and inverse maps. -/
@[stacks 04GS "canonical equivalence of chosen henselizations"]
noncomputable def algEquiv : Rh ≃ₐ[R] Sh :=
  algEquivOfLocal (lift (R := R) (Rh := Rh) (T := Sh))
    (lift (R := R) (Rh := Sh) (T := Rh))

/-- The canonical comparison supplies the historical existence statement. -/
@[stacks 04GS "equivalence of chosen henselizations"]
theorem nonemptyAlgEquiv : Nonempty (Rh ≃ₐ[R] Sh) := ⟨algEquiv⟩

/-- The comparison acts by the forward canonical lift. -/
@[simp]
theorem algEquiv_apply (a : Rh) :
    algEquiv (R := R) (Rh := Rh) (Sh := Sh) a =
      (lift (R := R) (Rh := Rh) (T := Sh)).hom a := rfl

/-- The inverse comparison acts by the reverse canonical lift. -/
@[simp]
theorem algEquiv_symm_apply (a : Sh) :
    (algEquiv (R := R) (Rh := Rh) (Sh := Sh)).symm a =
      (lift (R := R) (Rh := Sh) (T := Rh)).hom a := rfl

/-- The canonical comparison respects the structural maps from the base. -/
@[simp]
theorem algEquiv_apply_algebraMap (r : R) :
    algEquiv (R := R) (Rh := Rh) (Sh := Sh) (algebraMap R Rh r) = algebraMap R Sh r :=
  (algEquiv (R := R) (Rh := Rh) (Sh := Sh)).commutes r

/-- The inverse of the canonical comparison is the comparison in the reverse direction. -/
@[simp]
theorem algEquiv_symm :
    (algEquiv (R := R) (Rh := Rh) (Sh := Sh)).symm =
      algEquiv (R := R) (Rh := Sh) (Sh := Rh) := by
  ext a
  rfl

omit hCommSh hRSh hSh in
/-- Comparing a henselization with itself gives the identity. -/
@[simp]
theorem algEquiv_refl :
    algEquiv (R := R) (Rh := Rh) (Sh := Rh) = (AlgEquiv.refl : Rh ≃ₐ[R] Rh) := by
  ext a
  exact congrArg (fun f : AlgHom.Local (R := R) (A := Rh) (B := Rh) => f.hom a)
    (local_eq (lift (R := R) (Rh := Rh) (T := Rh))
      ⟨AlgHom.id R Rh, by change IsLocalHom (RingHom.id Rh); infer_instance⟩)

/-- The comparison transports residue fields through their canonical base identifications. -/
theorem algEquiv_residueFieldMap :
    (lift (R := R) (Rh := Rh) (T := Sh)).residueFieldMap =
      (residueFieldEquiv (R := R) (S := Sh)).toRingHom.comp
        (residueFieldEquiv (R := R) (S := Rh)).symm.toRingHom :=
  lift_residueFieldMap

/-- Canonical comparisons compose as expected. -/
theorem algEquiv_trans {Uh : Type x} [CommRing Uh] [Algebra R Uh]
    [IsHenselizationOf R Uh] :
    (algEquiv (R := R) (Rh := Rh) (Sh := Sh)).trans
        (algEquiv (R := R) (Rh := Sh) (Sh := Uh)) =
      algEquiv (R := R) (Rh := Rh) (Sh := Uh) := by
  ext a
  exact congrArg (fun f : Rh →ₐ[R] Uh => f a)
    (lift_naturality (R := R) (Rh := Rh) (T := Sh)
      (lift (R := R) (Rh := Sh) (T := Uh)))

omit hCommR hLocalR hCommRh hRRh hRh hCommSh hRSh hSh

end Equiv

section ResidueMap

variable {R : Type u} {S : Type v} {Rh : Type w} {Sh : Type x}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [IsLocalRing S]
variable [Algebra R S] [hRSLocal : IsLocalHom (algebraMap R S)]
variable [CommRing Rh] [Algebra R Rh] [hRh : IsHenselizationOf R Rh]
variable [CommRing Sh] [Algebra S Sh] [Algebra R Sh]
variable [hTower : IsScalarTower R S Sh] [hSh : IsHenselizationOf S Sh]

include hRSLocal hRh hSh hTower

/-- Tag 04GS: the residue-field map of a local comparison between chosen
henselizations is forced by the base residue-field map.  The displayed
formula is the neutral replacement for a construction-dependent choice of
separable-closure embeddings. -/
@[stacks 04GS "residue-field map of a henselization comparison"]
theorem residueFieldMap_eq_base
    (f : AlgHom.Local (R := R) (A := Rh) (B := Sh)) :
    f.residueFieldMap =
      (IsHenselizationOf.residueFieldEquiv (R := S) (S := Sh)).toRingHom.comp
        ((IsLocalRing.ResidueField.map (algebraMap R S)).comp
          (IsHenselizationOf.residueFieldEquiv (R := R) (S := Rh)).symm.toRingHom) := sorry

/-- Tag 04GS: if the base local map induces a bijection on residue fields,
then every local comparison between the corresponding henselizations does so
as well. -/
@[stacks 04GS "bijective residue-field map of a henselization comparison"]
theorem residueFieldMap_bijective_of_base
    (f : AlgHom.Local (R := R) (A := Rh) (B := Sh))
    (hκ : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R S))) :
    Function.Bijective f.residueFieldMap := sorry

end ResidueMap

end IsHenselizationOf
