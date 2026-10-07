module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.GradedSections.Localization.QuasiCompact
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Cohomology

/-!
# Localized twisted cohomology

The cohomology of all integral twists of a module forms a graded module over the section ring of
an invertible module. This file constructs its degree-zero homogeneous localization and the
canonical comparison with cohomology on the nonvanishing open of a section.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Modules.GradedSections

variable {X : Scheme.{u}}

/-- The degree-`n` piece of twisted degree-`p` cohomology is the `p`th cohomology of
`F ⊗ L^n`. -/
abbrev twistedCohomologyDegree
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ) (n : ℤ) : Type _ :=
  RingedSite.Hom.moduleGlobalCohomology
    (X := RingedSpace.opensRingedSite X.toRingedSpace) (F ⊗ (L ^⊗ n)) p

/-- A homogeneous section of `L^m` induces the coefficient morphism from the `n`th twist to the
`(m + n)`th twist. -/
noncomputable def twistedCohomologyActionMorphism
    (L : X.Modules) [Invertible L] (F : X.Modules) {m : ℕ} {n : ℤ}
    (r : RingedSpace.GradedSections.degree L m) :
    F ⊗ (L ^⊗ n) ⟶ F ⊗ (L ^⊗ ((m : ℤ) + n)) :=
  (λ_ (F ⊗ (L ^⊗ n))).inv ≫
    ((RingedSpace.unitIsoTensorUnit X.toRingedSpace).inv ≫
        RingedSpace.topSectionMorphism (RingedSpace.TensorPower.sheaf L m) r ⊗ₘ
      𝟙 (F ⊗ (L ^⊗ n))) ≫
    (RingedSpace.GradedSections.actionIso L F m n).hom

/-- The homogeneous action of a section on twisted cohomology, induced functorially by the
corresponding morphism of coefficient modules. -/
noncomputable def twistedCohomologySmul
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ) {m : ℕ} {n : ℤ} :
    RingedSpace.GradedSections.degree L m →
      twistedCohomologyDegree L F p n →
        twistedCohomologyDegree L F p ((m : ℤ) + n) :=
  fun r ξ ↦
    (RingedSite.Hom.moduleGlobalCohomologyMap
      (X := RingedSpace.opensRingedSite X.toRingedSpace)
      (twistedCohomologyActionMorphism L F r) p).hom ξ

/-- The integer-graded direct sum of the cohomology of all twists `F ⊗ L^n`. -/
abbrev twistedCohomology
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ) : Type _ :=
  ⨁ n : ℤ, twistedCohomologyDegree L F p n

/-- The explicit homogeneous cohomology action supplies graded scalar multiplication. -/
noncomputable instance instGSMulTwistedCohomology
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ) :
    GradedMonoid.GSMul
      (RingedSpace.GradedSections.degree L) (twistedCohomologyDegree L F p) where
  smul := fun r ξ ↦ twistedCohomologySmul L F p r ξ

/-- The graded unit acts trivially on twisted cohomology. -/
theorem twistedCohomology_one_smul
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ)
    (ξ : GradedMonoid (twistedCohomologyDegree L F p)) :
    (1 : GradedMonoid (RingedSpace.GradedSections.degree L)) • ξ = ξ := sorry

/-- Homogeneous multiplication is compatible with the action on twisted cohomology. -/
theorem twistedCohomology_mul_smul
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ)
    (a b : GradedMonoid (RingedSpace.GradedSections.degree L))
    (ξ : GradedMonoid (twistedCohomologyDegree L F p)) :
    (a * b) • ξ = a • b • ξ := sorry

/-- The twisted-cohomology pieces carry the graded multiplicative action of the section ring. -/
noncomputable instance instGMulActionTwistedCohomology
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ) :
    GradedMonoid.GMulAction
      (RingedSpace.GradedSections.degree L) (twistedCohomologyDegree L F p) where
  one_smul := twistedCohomology_one_smul L F p
  mul_smul := twistedCohomology_mul_smul L F p

/-- The homogeneous action distributes over addition of cohomology classes. -/
theorem twistedCohomology_smul_add
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ) {m : ℕ} {n : ℤ}
    (r : RingedSpace.GradedSections.degree L m)
    (ξ η : twistedCohomologyDegree L F p n) :
    twistedCohomologySmul L F p r (ξ + η) =
      twistedCohomologySmul L F p r ξ + twistedCohomologySmul L F p r η := sorry

/-- Every homogeneous section acts trivially on the zero cohomology class. -/
theorem twistedCohomology_smul_zero
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ) {m : ℕ} {n : ℤ}
    (r : RingedSpace.GradedSections.degree L m) :
    twistedCohomologySmul L F p r (0 : twistedCohomologyDegree L F p n) = 0 := sorry

/-- The homogeneous cohomology action is additive in the cohomology variable. -/
noncomputable instance instGdistribMulActionTwistedCohomology
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ) :
    DirectSum.GdistribMulAction
      (RingedSpace.GradedSections.degree L) (twistedCohomologyDegree L F p) where
  smul_add := twistedCohomology_smul_add L F p
  smul_zero := twistedCohomology_smul_zero L F p

/-- The homogeneous action distributes over addition of sections. -/
theorem twistedCohomology_add_smul
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ) {m : ℕ} {n : ℤ}
    (r t : RingedSpace.GradedSections.degree L m)
    (ξ : twistedCohomologyDegree L F p n) :
    twistedCohomologySmul L F p (r + t) ξ =
      twistedCohomologySmul L F p r ξ + twistedCohomologySmul L F p t ξ := sorry

/-- The zero homogeneous section acts trivially on twisted cohomology. -/
theorem twistedCohomology_zero_smul
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ) {m : ℕ} {n : ℤ}
    (ξ : twistedCohomologyDegree L F p n) :
    twistedCohomologySmul L F p
      (0 : RingedSpace.GradedSections.degree L m) ξ = 0 := sorry

/-- The twisted-cohomology pieces form a graded module over the tensor-power section ring. -/
noncomputable instance instGmoduleTwistedCohomology
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ) :
    DirectSum.Gmodule
      (RingedSpace.GradedSections.degree L) (twistedCohomologyDegree L F p) where
  add_smul := twistedCohomology_add_smul L F p
  zero_smul := twistedCohomology_zero_smul L F p

/-- Pure homogeneous summands act through the explicit twisted-cohomology action. -/
theorem twistedCohomology_of_smul_of
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ) {m : ℕ} {n : ℤ}
    (r : RingedSpace.GradedSections.degree L m)
    (ξ : twistedCohomologyDegree L F p n) :
    DirectSum.of (RingedSpace.GradedSections.degree L) m r •
        DirectSum.of (twistedCohomologyDegree L F p) n ξ =
      DirectSum.of (twistedCohomologyDegree L F p) ((m : ℤ) + n)
        (twistedCohomologySmul L F p r ξ) := sorry

/-- The degree-`n` homogeneous subgroup of twisted cohomology, restricted to nonnegative
degrees. -/
abbrev twistedCohomologyGrading
    (L : X.Modules) [Invertible L] (F : X.Modules) (p n : ℕ) :
    AddSubgroup (twistedCohomology L F p) :=
  AddMonoidHom.range (DirectSum.of (twistedCohomologyDegree L F p) (n : ℤ))

/-- Multiplication by a section of degree `i` sends twisted cohomology of degree `j` to degree
`i + j`. -/
theorem smul_mem_twistedCohomologyGrading
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ)
    {i j : ℕ} {r : RingedSpace.GradedSections.ring L}
    {ξ : twistedCohomology L F p}
    (hr : r ∈ RingedSpace.GradedSections.grading L i)
    (hξ : ξ ∈ twistedCohomologyGrading L F p j) :
    r • ξ ∈ twistedCohomologyGrading L F p (i + j) := sorry

/-- The section-ring grading acts compatibly on the nonnegative homogeneous subgroups of
twisted cohomology. -/
noncomputable instance instGradedSMulTwistedCohomologyGrading
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ) :
    SetLike.GradedSMul
      (RingedSpace.GradedSections.grading L) (twistedCohomologyGrading L F p) where
  smul_mem := fun i j r ξ hr hξ ↦ by
    simpa only [vadd_eq_add] using
      smul_mem_twistedCohomologyGrading L F p
        (i := i) (j := j) (r := r) (ξ := ξ) hr hξ

/-- The established degree-zero homogeneous localization in which two standard fractions are
compared. -/
abbrev localizedTwistedCohomologyAmbient
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) :=
  HomogeneousLocalization.Away.Module.degreeZeroPart
    (RingedSpace.GradedSections.grading L) (twistedCohomologyGrading L F p)
    (degreeOne L s)

/-- A standard degree-zero fraction consists of a denominator exponent `n` and a numerator in
the `n`th twisted-cohomology piece. -/
def localizedTwistedCohomologyFraction
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ)
    : Type _ :=
  Σ n : ℕ, twistedCohomologyDegree L F p (n : ℤ)

/-- The value of a standard fraction in homogeneous localization. -/
noncomputable def localizedTwistedCohomologyFractionToAmbient
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ)
    (q : localizedTwistedCohomologyFraction L F s p) :
    localizedTwistedCohomologyAmbient L F s p :=
  let numerator :=
    DirectSum.of (twistedCohomologyDegree L F p) (q.1 : ℤ) q.2
  have numerator_mem : numerator ∈ twistedCohomologyGrading L F p q.1 :=
    ⟨q.2, rfl⟩
  have denominatorDegreeNumerator_mem :
      numerator ∈ twistedCohomologyGrading L F p (q.1 • (1 : ℕ)) := by
    simpa using numerator_mem
  ⟨HomogeneousLocalization.Away.Module.powMk
      (RingedSpace.GradedSections.grading L) (degreeOne L s) q.1 numerator,
    HomogeneousLocalization.Away.Module.mk_mem_degreeZeroPart
      (RingedSpace.GradedSections.grading L) (twistedCohomologyGrading L F p)
      (degreeOne L s) denominatorDegreeNumerator_mem⟩

/-- Two standard fractions are equivalent exactly when they determine the same element of
homogeneous localization. -/
noncomputable abbrev localizedTwistedCohomologyFractionSetoid
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) :
    Setoid (localizedTwistedCohomologyFraction L F s p) where
  r q q' := localizedTwistedCohomologyFractionToAmbient L F s p q =
    localizedTwistedCohomologyFractionToAmbient L F s p q'
  iseqv := ⟨fun _ ↦ rfl, fun h ↦ h.symm, fun h h' ↦ h.trans h'⟩

/-- The degree-zero localization of twisted cohomology, represented without choosing standard
fraction representatives. -/
def localizedTwistedCohomology
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) :
    Type _ :=
  Quotient (localizedTwistedCohomologyFractionSetoid L F s p)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A twisted-cohomology piece is additively equivalent to its homogeneous summand in the
graded direct sum. -/
private def twistedCohomologySummandEquiv
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ) (n : ℤ) :
    twistedCohomologyDegree L F p n ≃+
      AddMonoidHom.range (DirectSum.of (twistedCohomologyDegree L F p) n) where
  toFun ξ := ⟨DirectSum.of (twistedCohomologyDegree L F p) n ξ, ⟨ξ, rfl⟩⟩
  invFun ξ := DirectSum.component ℤ ℤ (twistedCohomologyDegree L F p) n ξ.1
  left_inv ξ := DirectSum.component.lof_self (R := ℤ) n ξ
  right_inv ξ := by
    obtain ⟨η, hη⟩ := ξ.2
    apply Subtype.ext
    change DirectSum.of (twistedCohomologyDegree L F p) n
        (DirectSum.component ℤ ℤ (twistedCohomologyDegree L F p) n ξ.1) = ξ.1
    rw [← hη]
    exact congrArg (DirectSum.of (twistedCohomologyDegree L F p) n)
      (DirectSum.component.lof_self (R := ℤ) n η)
  map_add' ξ η := by
    apply Subtype.ext
    simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Re-embedding the external representative of an internal twisted-cohomology summand returns
the original direct-sum element. -/
private theorem twistedCohomologySummandEquiv_symm_apply
    (L : X.Modules) [Invertible L] (F : X.Modules) (p : ℕ) (n : ℤ)
    (ξ : AddMonoidHom.range (DirectSum.of (twistedCohomologyDegree L F p) n)) :
    DirectSum.of (twistedCohomologyDegree L F p) n
        ((twistedCohomologySummandEquiv L F p n).symm ξ) = ξ.1 :=
  congrArg Subtype.val ((twistedCohomologySummandEquiv L F p n).apply_symm_apply ξ)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The numerator obtained by bringing two standard fractions to the product of their
denominator powers. -/
private noncomputable def localizedTwistedCohomologyFractionAddNumerator
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ)
    (q q' : localizedTwistedCohomologyFraction L F s p) :
    twistedCohomologyDegree L F p ((q.1 + q'.1 : ℕ) : ℤ) :=
  let numerator : twistedCohomologyGrading L F p (q.1 + q'.1) :=
    ⟨(degreeOne L s : RingedSpace.GradedSections.ring L) ^ q'.1 •
          DirectSum.of (twistedCohomologyDegree L F p) (q.1 : ℤ) q.2 +
        (degreeOne L s : RingedSpace.GradedSections.ring L) ^ q.1 •
          DirectSum.of (twistedCohomologyDegree L F p) (q'.1 : ℤ) q'.2,
      by
        apply AddSubgroup.add_mem
        · simpa [add_comm] using
            smul_mem_twistedCohomologyGrading L F p
              (i := q'.1) (j := q.1)
              (r := (degreeOne L s : RingedSpace.GradedSections.ring L) ^ q'.1)
              (ξ := DirectSum.of (twistedCohomologyDegree L F p) (q.1 : ℤ) q.2)
              (by simpa using SetLike.pow_mem_graded q'.1 (degreeOne L s).2) ⟨q.2, rfl⟩
        · exact
            smul_mem_twistedCohomologyGrading L F p
              (i := q.1) (j := q'.1)
              (r := (degreeOne L s : RingedSpace.GradedSections.ring L) ^ q.1)
              (ξ := DirectSum.of (twistedCohomologyDegree L F p) (q'.1 : ℤ) q'.2)
              (by simpa using SetLike.pow_mem_graded q.1 (degreeOne L s).2) ⟨q'.2, rfl⟩⟩
  (twistedCohomologySummandEquiv L F p ((q.1 + q'.1 : ℕ) : ℤ)).symm numerator

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Addition of standard fractions after passage to a common power of the denominator. -/
private noncomputable def localizedTwistedCohomologyFractionAdd
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ)
    (q q' : localizedTwistedCohomologyFraction L F s p) :
    localizedTwistedCohomologyFraction L F s p :=
  ⟨q.1 + q'.1,
    localizedTwistedCohomologyFractionAddNumerator L F s p q q'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The zero standard fraction. -/
private def localizedTwistedCohomologyFractionZero
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) :
    localizedTwistedCohomologyFraction L F s p :=
  ⟨0, 0⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Common-denominator addition of standard fractions agrees with addition in homogeneous
localization. -/
private theorem localizedTwistedCohomologyFractionToAmbient_add
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ)
    (q q' : localizedTwistedCohomologyFraction L F s p) :
    localizedTwistedCohomologyFractionToAmbient L F s p
        (localizedTwistedCohomologyFractionAdd L F s p q q') =
      localizedTwistedCohomologyFractionToAmbient L F s p q +
        localizedTwistedCohomologyFractionToAmbient L F s p q' := by
  apply Subtype.ext
  change (localizedTwistedCohomologyFractionToAmbient L F s p
      (localizedTwistedCohomologyFractionAdd L F s p q q')).1 =
    (localizedTwistedCohomologyFractionToAmbient L F s p q).1 +
      (localizedTwistedCohomologyFractionToAmbient L F s p q').1
  simp only [localizedTwistedCohomologyFractionAdd,
    localizedTwistedCohomologyFractionToAmbient]
  rw [LocalizedModule.mk_add_mk]
  simp only [HomogeneousLocalization.Away.Module.powMk]
  congr 1
  · simp only [localizedTwistedCohomologyFractionAddNumerator]
    apply twistedCohomologySummandEquiv_symm_apply
  · apply Subtype.ext
    simp [pow_add]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The zero standard fraction represents zero in homogeneous localization. -/
private theorem localizedTwistedCohomologyFractionToAmbient_zero
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) :
    localizedTwistedCohomologyFractionToAmbient L F s p
      (localizedTwistedCohomologyFractionZero L F s p) = 0 := by
  apply Subtype.ext
  simp [localizedTwistedCohomologyFractionZero,
    localizedTwistedCohomologyFractionToAmbient,
    HomogeneousLocalization.Away.Module.powMk]

/-- A localized twisted-cohomology class determines its value in homogeneous localization. -/
noncomputable def localizedTwistedCohomologyToAmbient
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) :
    localizedTwistedCohomology L F s p → localizedTwistedCohomologyAmbient L F s p :=
  Quotient.lift (localizedTwistedCohomologyFractionToAmbient L F s p) (fun _ _ h ↦ by
    exact h)

/-- Equality in homogeneous localization detects equality of localized twisted-cohomology
classes. -/
theorem localizedTwistedCohomologyToAmbient_injective
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) :
    Function.Injective (localizedTwistedCohomologyToAmbient L F s p) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | _ q =>
      induction y using Quotient.inductionOn with
      | _ q' =>
          change localizedTwistedCohomologyFractionToAmbient L F s p q =
            localizedTwistedCohomologyFractionToAmbient L F s p q' at h
          apply Quotient.sound
          exact h

/-- Standard homogeneous fractions exhaust the established degree-zero homogeneous
localization. -/
theorem localizedTwistedCohomologyToAmbient_bijective
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) :
    Function.Bijective (localizedTwistedCohomologyToAmbient L F s p) := sorry

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The zero localized twisted-cohomology class is represented by the zero standard fraction. -/
noncomputable instance instZeroLocalizedTwistedCohomology
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) :
    Zero (localizedTwistedCohomology L F s p) :=
  ⟨Quotient.mk _ (localizedTwistedCohomologyFractionZero L F s p)⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Localized twisted-cohomology classes add by bringing standard fractions to a common
denominator. -/
noncomputable instance instAddLocalizedTwistedCohomology
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) :
    Add (localizedTwistedCohomology L F s p) where
  add := Quotient.map₂ (localizedTwistedCohomologyFractionAdd L F s p) fun q r h q' r' h' ↦ by
    change localizedTwistedCohomologyFractionToAmbient L F s p
        (localizedTwistedCohomologyFractionAdd L F s p q q') =
      localizedTwistedCohomologyFractionToAmbient L F s p
        (localizedTwistedCohomologyFractionAdd L F s p r r')
    have hq : localizedTwistedCohomologyFractionToAmbient L F s p q =
        localizedTwistedCohomologyFractionToAmbient L F s p r := by
      exact h
    have hq' : localizedTwistedCohomologyFractionToAmbient L F s p q' =
        localizedTwistedCohomologyFractionToAmbient L F s p r' := by
      exact h'
    rw [localizedTwistedCohomologyFractionToAmbient_add,
      localizedTwistedCohomologyFractionToAmbient_add, hq, hq']

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The map from localized twisted cohomology to homogeneous localization preserves zero. -/
private theorem localizedTwistedCohomologyToAmbient_zero
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) :
    localizedTwistedCohomologyToAmbient L F s p 0 = 0 := by
  change localizedTwistedCohomologyFractionToAmbient L F s p
    (localizedTwistedCohomologyFractionZero L F s p) = 0
  exact localizedTwistedCohomologyFractionToAmbient_zero L F s p

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The map from localized twisted cohomology to homogeneous localization preserves addition. -/
private theorem localizedTwistedCohomologyToAmbient_add
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ)
    (x y : localizedTwistedCohomology L F s p) :
    localizedTwistedCohomologyToAmbient L F s p (x + y) =
      localizedTwistedCohomologyToAmbient L F s p x +
        localizedTwistedCohomologyToAmbient L F s p y := by
  induction x using Quotient.inductionOn with
  | _ q =>
      induction y using Quotient.inductionOn with
      | _ q' =>
          change localizedTwistedCohomologyFractionToAmbient L F s p
              (localizedTwistedCohomologyFractionAdd L F s p q q') =
            localizedTwistedCohomologyFractionToAmbient L F s p q +
              localizedTwistedCohomologyFractionToAmbient L F s p q'
          exact localizedTwistedCohomologyFractionToAmbient_add L F s p q q'

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The fraction quotient carries the additive commutative-monoid structure inherited from
homogeneous localization. -/
noncomputable instance instAddCommMonoidLocalizedTwistedCohomology
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) :
    AddCommMonoid (localizedTwistedCohomology L F s p) where
  add_assoc x y z := localizedTwistedCohomologyToAmbient_injective L F s p <| by
    simp only [localizedTwistedCohomologyToAmbient_add, add_assoc]
  zero_add x := localizedTwistedCohomologyToAmbient_injective L F s p <| by
    simp only [localizedTwistedCohomologyToAmbient_add,
      localizedTwistedCohomologyToAmbient_zero, zero_add]
  add_zero x := localizedTwistedCohomologyToAmbient_injective L F s p <| by
    simp only [localizedTwistedCohomologyToAmbient_add,
      localizedTwistedCohomologyToAmbient_zero, add_zero]
  add_comm x y := localizedTwistedCohomologyToAmbient_injective L F s p <| by
    simp only [localizedTwistedCohomologyToAmbient_add, add_comm]
  nsmul := nsmulRec
  nsmul_zero := fun _ ↦ rfl
  nsmul_succ := fun _ _ ↦ rfl

/-- The standard degree-zero localized cohomology fraction `ξ / s^n`. -/
noncomputable def localizedTwistedCohomologyMk
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ)
    (n : ℕ) (ξ : twistedCohomologyDegree L F p (n : ℤ)) :
    localizedTwistedCohomology L F s p :=
  Quotient.mk _ ⟨n, ξ⟩

/-- Every localized twisted-cohomology class admits a standard homogeneous fraction
representative. -/
theorem exists_localizedTwistedCohomologyMk_eq
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ)
    (z : localizedTwistedCohomology L F s p) :
    ∃ n : ℕ, ∃ ξ : twistedCohomologyDegree L F p (n : ℤ),
      z = localizedTwistedCohomologyMk L F s p n ξ := sorry

/-- Additive maps out of localized twisted cohomology agree when they agree on all standard
homogeneous fractions. -/
theorem localizedTwistedCohomology_hom_ext
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ)
    {A : Type v} [AddCommMonoid A]
    {f g : localizedTwistedCohomology L F s p →+ A}
    (h : ∀ n : ℕ, ∀ ξ : twistedCohomologyDegree L F p (n : ℤ),
      f (localizedTwistedCohomologyMk L F s p n ξ) =
        g (localizedTwistedCohomologyMk L F s p n ξ)) :
    f = g := sorry

/-- Cohomology of `F` on the nonvanishing open of a section, computed on the corresponding
localized ringed site. -/
abbrev nonvanishingOpenCohomology
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) : Type _ :=
  let U := RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
    (RingedSpace.sectionFromTop L s)
  @RingedSite.Hom.moduleGlobalCohomology
    ((RingedSpace.opensRingedSite X.toRingedSpace).localization U) _
    (RingedSite.Hom.localizedModuleCatHasExt
      (X := RingedSpace.opensRingedSite X.toRingedSpace) U) (F.over U) p

/-- The cohomology class on the nonvanishing open represented by `ξ / s^n`: restrict the
class to the localized site and contract its tensor-power factor by the inverse power of `s`. -/
noncomputable def localizedTwistedCohomologyFractionValue
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p n : ℕ)
    (ξ : twistedCohomologyDegree L F p (n : ℤ)) :
    nonvanishingOpenCohomology L F s p :=
  let U := RingedSpace.sectionNonvanishingOpen X.toRingedSpace L
    (RingedSpace.sectionFromTop L s)
  let R := RingedSite.Hom.localizedRestriction
    (RingedSpace.opensRingedSite X.toRingedSpace) U
  let G := F ⊗ (L ^⊗ (n : ℤ))
  let hExt : HasExt.{u} (RingedSite.ModuleCat
      ((RingedSpace.opensRingedSite X.toRingedSpace).localization U)) :=
    RingedSite.Hom.localizedModuleCatHasExt
      (X := RingedSpace.opensRingedSite X.toRingedSpace) U
  let unitComparison :
      SheafOfModules.unit
          ((RingedSpace.opensRingedSite X.toRingedSpace).localization U).structureSheaf ⟶
        R.obj (SheafOfModules.unit
          (RingedSpace.opensRingedSite X.toRingedSpace).structureSheaf) :=
    (SheafOfModules.RingedSite.unitIsoTensorUnit
      (J := ((RingedSpace.opensRingedSite X.toRingedSpace).localization U).siteTopology)
      (𝒪 := X.toRingedSpace.sheaf.over U)).hom ≫
      (Functor.Monoidal.εIso R).hom ≫
      R.map (SheafOfModules.RingedSite.unitIsoTensorUnit
        (J := (RingedSpace.opensRingedSite X.toRingedSpace).siteTopology)
        (𝒪 := X.toRingedSpace.sheaf)).inv
  let restricted : @Ext _ _ _ hExt
      (SheafOfModules.unit
        ((RingedSpace.opensRingedSite X.toRingedSpace).localization U).structureSheaf)
      (R.obj G) p :=
    ((@Ext.precomp _ _ _ hExt _ _ _
      (@Ext.mk₀ _ _ _ hExt _ _ unitComparison)
      (R.obj G) _ _ (zero_add p))
      ((@Functor.mapExtAddHom _ _ _ _ _ _ R
        (RingedSite.Hom.localizedRestriction_additive
          (RingedSpace.opensRingedSite X.toRingedSpace) U)
        (RingedSite.Hom.localizedRestriction_preservesFiniteLimits
          (RingedSpace.opensRingedSite X.toRingedSpace) U)
        (RingedSite.Hom.localizedRestriction_preservesFiniteColimits
          (RingedSpace.opensRingedSite X.toRingedSpace) U) _
        hExt
        (SheafOfModules.unit
          (RingedSpace.opensRingedSite X.toRingedSpace).structureSheaf) G p) ξ))
  (@Ext.postcomp _ _ _ hExt _ _ _
    (@Ext.mk₀ _ _ _ hExt _ _
      (Invertible.nonvanishingTwistContraction L F s n))
    (SheafOfModules.unit
      ((RingedSpace.opensRingedSite X.toRingedSpace).localization U).structureSheaf)
    _ _ (add_zero p)) restricted

/-- Equal standard localized cohomology fractions have equal restriction-and-contraction
values on the nonvanishing open. -/
theorem localizedTwistedCohomologyFractionValue_eq_of_mk_eq
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ)
    {n n' : ℕ}
    {ξ : twistedCohomologyDegree L F p (n : ℤ)}
    {ξ' : twistedCohomologyDegree L F p (n' : ℤ)}
    (h : localizedTwistedCohomologyMk L F s p n ξ =
      localizedTwistedCohomologyMk L F s p n' ξ') :
    localizedTwistedCohomologyFractionValue L F s p n ξ =
      localizedTwistedCohomologyFractionValue L F s p n' ξ' := sorry

/-- The comparison function evaluates a localized cohomology class through a standard
homogeneous fraction representative. -/
noncomputable def localizedTwistedCohomologyComparisonFun
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) :
    localizedTwistedCohomology L F s p → nonvanishingOpenCohomology L F s p :=
  Quotient.lift
    (fun q ↦ localizedTwistedCohomologyFractionValue L F s p q.1 q.2)
    (fun q q' h ↦
      localizedTwistedCohomologyFractionValue_eq_of_mk_eq L F s p
        (Quotient.sound h))

/-- The localized twisted-cohomology comparison function sends zero to zero. -/
theorem localizedTwistedCohomologyComparisonFun_map_zero
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) :
    localizedTwistedCohomologyComparisonFun L F s p 0 = 0 := sorry

/-- The localized twisted-cohomology comparison function preserves addition. -/
theorem localizedTwistedCohomologyComparisonFun_map_add
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ)
    (x y : localizedTwistedCohomology L F s p) :
    localizedTwistedCohomologyComparisonFun L F s p (x + y) =
      localizedTwistedCohomologyComparisonFun L F s p x +
        localizedTwistedCohomologyComparisonFun L F s p y := sorry

/-- The canonical additive comparison from localized twisted cohomology to cohomology on the
nonvanishing open. -/
noncomputable def localizedTwistedCohomologyComparison
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p : ℕ) :
    localizedTwistedCohomology L F s p →+ nonvanishingOpenCohomology L F s p where
  toFun := localizedTwistedCohomologyComparisonFun L F s p
  map_zero' := localizedTwistedCohomologyComparisonFun_map_zero L F s p
  map_add' := localizedTwistedCohomologyComparisonFun_map_add L F s p

/-- On a standard fraction, the localized comparison restricts its numerator and contracts the
twist by the inverse power of the nonvanishing section. -/
theorem localizedTwistedCohomologyComparison_apply_mk
    (L : X.Modules) [Invertible L] (F : X.Modules) (s : Γ(L, ⊤)) (p n : ℕ)
    (ξ : twistedCohomologyDegree L F p (n : ℤ)) :
    localizedTwistedCohomologyComparison L F s p
        (localizedTwistedCohomologyMk L F s p n ξ) =
      localizedTwistedCohomologyFractionValue L F s p n ξ := sorry

/-- On a quasi-compact and quasi-separated scheme, localized twisted cohomology is canonically
identified with cohomology on the nonvanishing open. -/
theorem localizedTwistedCohomologyComparison_bijective
    [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [Invertible L]
    (F : X.Modules) [F.IsQuasicoherent] (s : Γ(L, ⊤)) (p : ℕ) :
    Function.Bijective (localizedTwistedCohomologyComparison L F s p) := sorry

end AlgebraicGeometry.Scheme.Modules.GradedSections
