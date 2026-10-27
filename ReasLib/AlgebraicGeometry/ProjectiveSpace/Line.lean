/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Tactic.CrossRefAttribute

/-!
# The projective line

This file specializes the standard projective-space construction to dimension one. It owns
the two standard affine charts and the basic global properties used across later chapters.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLine

section CommRing

variable (R : Type u) [CommRing R]

/-- The standard projective line over `R`. -/
@[stacks 01JE "projective line"]
abbrev scheme : Scheme.{u} := ProjectiveSpace.scheme R 1

/-- The standard structure morphism from the projective line to `Spec R`. -/
@[stacks 01JE "projective-line structure morphism"]
abbrev toSpec : scheme R ⟶ Spec (.of R) := ProjectiveSpace.toSpec R 1

/-- The projective-line structure morphism is separated over every commutative base ring. This
named theorem exposes the canonical instance without registering a duplicate instance. -/
@[stacks 01KQ "projective line is separated over its base"]
theorem toSpec_isSeparated : IsSeparated (toSpec R) := by
  dsimp [toSpec, ProjectiveSpace.toSpec]
  infer_instance

/-- The affine line model used for the two standard projective-line charts. -/
@[stacks 01JE "projective-line affine chart model"]
abbrev affineLine : Scheme.{u} :=
  𝔸(ULift.{u} (Fin 1); Spec (CommRingCat.of R))

/-- The standard grading on the two-variable polynomial ring over `R`. -/
@[stacks 01JE "projective-line grading"]
abbrev grading : ℕ → Submodule R (MvPolynomial (Fin 2) R) :=
  ProjectiveSpace.grading R 1

/-- A homogeneous coordinate on the standard projective line. -/
@[stacks 01JE "projective-line homogeneous coordinate"]
abbrev coordinate (i : Fin 2) : MvPolynomial (Fin 2) R :=
  ProjectiveSpace.coordinate (R := R) 1 i

/-- The first homogeneous coordinate on the projective line. -/
@[stacks 01JE "projective-line first coordinate"]
abbrev x : MvPolynomial (Fin 2) R := coordinate R 0

/-- The second homogeneous coordinate on the projective line. -/
@[stacks 01JE "projective-line second coordinate"]
abbrev y : MvPolynomial (Fin 2) R := coordinate R 1

/-- The standard chart `D₊(X)` on the projective line. -/
@[stacks 01JE "projective-line X chart affine open"]
abbrev chartXAffine : (scheme R).affineOpens :=
  ProjectiveSpace.coordinateBasicOpen (R := R) 1 0

/-- The standard chart `D₊(X)` as an open subset. -/
@[stacks 01JE "projective-line X chart"]
abbrev chartX : (scheme R).Opens :=
  chartXAffine R

/-- The standard chart `D₊(Y)` on the projective line. -/
@[stacks 01JE "projective-line Y chart affine open"]
abbrev chartYAffine : (scheme R).affineOpens :=
  ProjectiveSpace.coordinateBasicOpen (R := R) 1 1

/-- The standard chart `D₊(Y)` as an open subset. -/
@[stacks 01JE "projective-line Y chart"]
abbrev chartY : (scheme R).Opens :=
  chartYAffine R

/-- The concrete `X`-chart isomorphism with the affine-line model. -/
@[stacks 01JE "first affine chart isomorphism"]
noncomputable abbrev chartXIso : (chartX R).toScheme ≅ affineLine R :=
  ProjectiveSpace.CoordinateChart.iso (R := R) 1 0

/-- The forward morphism of the concrete `X`-chart isomorphism to the affine-line model. -/
@[stacks 01JE "first affine chart comparison"]
noncomputable abbrev chartXComparison : (chartX R).toScheme ⟶ affineLine R :=
  (chartXIso R).hom

/-- The concrete `Y`-chart isomorphism with the affine-line model. -/
@[stacks 01JE "second affine chart isomorphism"]
noncomputable abbrev chartYIso : (chartY R).toScheme ≅ affineLine R :=
  ProjectiveSpace.CoordinateChart.iso (R := R) 1 1

/-- The forward morphism of the concrete `Y`-chart isomorphism to the affine-line model. -/
@[stacks 01JE "second affine chart comparison"]
noncomputable abbrev chartYComparison : (chartY R).toScheme ⟶ affineLine R :=
  (chartYIso R).hom

private theorem chartComparison_toSpec (i : Fin 2) :
    (ProjectiveSpace.CoordinateChart.iso (R := R) 1 i).hom ≫
      (𝔸(ULift.{u} (Fin 1); Spec (CommRingCat.of R)) ↘ Spec (CommRingCat.of R)) =
      (ProjectiveSpace.coordinateBasicOpen (R := R) 1 i).1.ι ≫
        ProjectiveSpace.toSpec R 1 := by
  apply (cancel_epi (Proj.basicOpenIsoSpec (ProjectiveSpace.grading R 1)
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one).inv).mp
  simp only [ProjectiveSpace.CoordinateChart.iso, ProjectiveSpace.CoordinateChart.isoWith,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.op_inv, Scheme.Spec_map,
    Category.assoc, Iso.inv_hom_id_assoc]
  erw [AffineSpace.SpecIso_inv_over (n := ULift.{u} (Fin 1)) (CommRingCat.of R)]
  erw [← Category.assoc, Proj.basicOpenIsoSpec_inv_ι]
  simp only [ProjectiveSpace.toSpec, Proj.awayι_toSpecZero_assoc]
  simp only [ProjectiveSpace.degreeZeroSpecIso, Iso.symm_hom, Functor.mapIso_inv,
    Iso.op_inv, Scheme.Spec_map, Quiver.Hom.unop_op, ← Spec.map_comp]
  erw [← Spec.map_comp]
  congr 1
  ext r : 2
  change ProjectiveSpace.affineChartHom (R := R) 1 i Equiv.ulift.symm (MvPolynomial.C r) = _
  simp [ProjectiveSpace.affineChartHom, ProjectiveSpace.coefficientToCoordinateAway,
    ProjectiveSpace.degreeZeroRingEquiv, ProjectiveSpace.degreeZeroC]
  congr 1

/-- The zero section of the affine-line model. -/
@[stacks 01JE "affine-line zero section"]
noncomputable def affineLineZero : Spec (CommRingCat.of R) ⟶ affineLine R :=
  AffineSpace.homOfVector (𝟙 _) (fun _ ↦ 0)

private theorem affineLineZero_spec :
    affineLineZero R ≫ (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of R)).hom =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.eval₂Hom (RingHom.id R) (fun _ : ULift.{u} (Fin 1) ↦ 0))) := by
  apply (cancel_mono (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of R)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply AffineSpace.hom_ext
  · simp only [affineLineZero, AffineSpace.homOfVector_over,
      Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
    symm
    rw [Spec.map_eq_id]
    ext r : 2
    simp
  · intro j
    rw [affineLineZero, AffineSpace.homOfVector_appTop_coord,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply,
      ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    change 0 = (Scheme.ΓSpecIso (CommRingCat.of R)).inv
      ((MvPolynomial.eval₂Hom (RingHom.id R) (fun _ : ULift.{u} (Fin 1) ↦ 0)) (MvPolynomial.X j))
    simp only [MvPolynomial.eval₂Hom_X', map_zero]

/-- The unit section of the affine-line model. -/
@[stacks 01JE "affine-line unit section"]
noncomputable def affineLineOne : Spec (CommRingCat.of R) ⟶ affineLine R :=
  AffineSpace.homOfVector (𝟙 _) (fun _ ↦ 1)

/-- The canonical section `[1 : 0]` of the projective line, obtained from the affine zero
section on the `X`-chart. -/
@[stacks 01JE "zero section"]
noncomputable def zeroSection : Spec (CommRingCat.of R) ⟶ scheme R :=
  affineLineZero R ≫
    (ProjectiveSpace.CoordinateChart.iso (R := R) 1 0).inv ≫ (chartX R).ι

/-- A section is the standard section `[1 : 0]` when it is induced by the affine zero section on
the `X`-chart. -/
@[stacks 01JE "zero section specification"]
def IsZeroSection (s : Spec (CommRingCat.of R) ⟶ scheme R) : Prop :=
  ∃ t : Spec (CommRingCat.of R) ⟶ (chartX R).toScheme,
    t ≫ chartXComparison R = affineLineZero R ∧ t ≫ (chartX R).ι = s

/-- The canonical zero section satisfies its `X`-chart specification. -/
@[stacks 01JE "zero section specification witness"]
theorem zeroSection_isZeroSection : IsZeroSection R (zeroSection R) := by
  refine ⟨affineLineZero R ≫ (chartXIso R).inv, ?_, rfl⟩
  simp [chartXComparison]

/-- The `X`-chart specification characterizes the canonical zero section. -/
@[stacks 01JE "zero section specification characterization"]
theorem isZeroSection_iff_eq (s : Spec (CommRingCat.of R) ⟶ scheme R) :
    IsZeroSection R s ↔ s = zeroSection R := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht' : t = affineLineZero R ≫ (chartXIso R).inv := by
      rw [← ht]
      simp [chartXComparison]
    rw [ht']
    rfl
  · rintro rfl
    exact zeroSection_isZeroSection R

/-- A zero section is a section of the projective-line structure morphism. -/
@[stacks 01JE "zero section over the base"]
theorem IsZeroSection.toSpec {s : Spec (CommRingCat.of R) ⟶ scheme R}
    (hs : IsZeroSection R s) : s ≫ toSpec R = 𝟙 _ := by
  obtain ⟨t, ht, rfl⟩ := hs
  rw [Category.assoc, ← chartComparison_toSpec R 0,
    ← Category.assoc, ht]
  exact AffineSpace.homOfVector_over _ _

/-- The canonical zero section splits the projective-line structure morphism. -/
@[simp, stacks 01JE "zero section structure map"]
theorem zeroSection_toSpec : zeroSection R ≫ toSpec R = 𝟙 _ :=
  (zeroSection_isZeroSection R).toSpec R

/-- The canonical section `[0 : 1]` of the projective line, obtained from the affine zero
section on the `Y`-chart. -/
@[stacks 01JE "infinity section"]
noncomputable def infinitySection : Spec (CommRingCat.of R) ⟶ scheme R :=
  affineLineZero R ≫
    (ProjectiveSpace.CoordinateChart.iso (R := R) 1 1).inv ≫ (chartY R).ι

/-- A section is the standard section `[0 : 1]` when it is induced by the affine zero section on
the `Y`-chart. -/
@[stacks 01JE "infinity section specification"]
def IsInfinitySection (s : Spec (CommRingCat.of R) ⟶ scheme R) : Prop :=
  ∃ t : Spec (CommRingCat.of R) ⟶ (chartY R).toScheme,
    t ≫ chartYComparison R = affineLineZero R ∧ t ≫ (chartY R).ι = s

/-- The canonical infinity section satisfies its `Y`-chart specification. -/
@[stacks 01JE "infinity section specification witness"]
theorem infinitySection_isInfinitySection :
    IsInfinitySection R (infinitySection R) := by
  refine ⟨affineLineZero R ≫ (chartYIso R).inv, ?_, rfl⟩
  simp [chartYComparison]

/-- The `Y`-chart specification characterizes the canonical infinity section. -/
@[stacks 01JE "infinity section specification characterization"]
theorem isInfinitySection_iff_eq (s : Spec (CommRingCat.of R) ⟶ scheme R) :
    IsInfinitySection R s ↔ s = infinitySection R := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht' : t = affineLineZero R ≫ (chartYIso R).inv := by
      rw [← ht]
      simp [chartYComparison]
    rw [ht']
    rfl
  · rintro rfl
    exact infinitySection_isInfinitySection R

/-- An infinity section is a section of the projective-line structure morphism. -/
@[stacks 01JE "infinity section over the base"]
theorem IsInfinitySection.toSpec {s : Spec (CommRingCat.of R) ⟶ scheme R}
    (hs : IsInfinitySection R s) : s ≫ toSpec R = 𝟙 _ := by
  obtain ⟨t, ht, rfl⟩ := hs
  rw [Category.assoc, ← chartComparison_toSpec R 1,
    ← Category.assoc, ht]
  exact AffineSpace.homOfVector_over _ _

/-- The canonical infinity section splits the projective-line structure morphism. -/
@[simp, stacks 01JE "infinity section structure map"]
theorem infinitySection_toSpec : infinitySection R ≫ toSpec R = 𝟙 _ :=
  (infinitySection_isInfinitySection R).toSpec R

/-- The canonical section `[1 : 1]` of the projective line, obtained from the affine unit
section on the `X`-chart. -/
@[stacks 01JE "one section"]
noncomputable def oneSection : Spec (CommRingCat.of R) ⟶ scheme R :=
  affineLineOne R ≫
    (ProjectiveSpace.CoordinateChart.iso (R := R) 1 0).inv ≫ (chartX R).ι

/-- A section is the standard section `[1 : 1]` when it is induced by the affine unit section on
the `X`-chart. -/
@[stacks 01JE "one section specification"]
def IsOneSection (s : Spec (CommRingCat.of R) ⟶ scheme R) : Prop :=
  ∃ t : Spec (CommRingCat.of R) ⟶ (chartX R).toScheme,
    t ≫ chartXComparison R = affineLineOne R ∧ t ≫ (chartX R).ι = s

/-- The canonical one section satisfies its `X`-chart specification. -/
@[stacks 01JE "one section specification witness"]
theorem oneSection_isOneSection : IsOneSection R (oneSection R) := by
  refine ⟨affineLineOne R ≫ (chartXIso R).inv, ?_, rfl⟩
  simp [chartXComparison]

/-- The `X`-chart specification characterizes the canonical one section. -/
@[stacks 01JE "one section specification characterization"]
theorem isOneSection_iff_eq (s : Spec (CommRingCat.of R) ⟶ scheme R) :
    IsOneSection R s ↔ s = oneSection R := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht' : t = affineLineOne R ≫ (chartXIso R).inv := by
      rw [← ht]
      simp [chartXComparison]
    rw [ht']
    rfl
  · rintro rfl
    exact oneSection_isOneSection R

/-- A one section is a section of the projective-line structure morphism. -/
@[stacks 01JE "one section over the base"]
theorem IsOneSection.toSpec {s : Spec (CommRingCat.of R) ⟶ scheme R}
    (hs : IsOneSection R s) : s ≫ toSpec R = 𝟙 _ := by
  obtain ⟨t, ht, rfl⟩ := hs
  rw [Category.assoc, ← chartComparison_toSpec R 0,
    ← Category.assoc, ht]
  exact AffineSpace.homOfVector_over _ _

/-- The canonical one section splits the projective-line structure morphism. -/
@[simp, stacks 01JE "one section structure map"]
theorem oneSection_toSpec : oneSection R ≫ toSpec R = 𝟙 _ :=
  (oneSection_isOneSection R).toSpec R

/-- The two standard affine charts cover the projective line. -/
@[stacks 01JE "standard affine cover"]
theorem charts_cover : chartX R ⊔ chartY R = ⊤ := by
  have hgen : Algebra.adjoin (grading R 0)
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) R)) = ⊤ := by
    apply top_unique
    intro p hp
    clear hp
    induction p using MvPolynomial.induction_on with
    | C r =>
      exact (Algebra.adjoin (grading R 0) _).algebraMap_mem
        (ProjectiveSpace.degreeZeroC R 1 r)
    | add p q hp hq => exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp =>
      exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (Set.mem_range_self i))
  have hcover := Proj.iSup_basicOpen_eq_top' (grading R) MvPolynomial.X
    (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X R i⟩) hgen
  apply top_unique
  rw [← hcover]
  refine iSup_le fun i ↦ ?_
  refine Fin.cases le_sup_left (fun j ↦ ?_) i
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact le_sup_right

/-- The standard chart `D₊(X)` is affine. -/
@[stacks 01JE "projective-line X chart affineness"]
theorem chartX_isAffineOpen : IsAffineOpen (chartX R) :=
  (chartXAffine R).2

/-- The standard chart `D₊(Y)` is affine. -/
@[stacks 01JE "projective-line Y chart affineness"]
theorem chartY_isAffineOpen : IsAffineOpen (chartY R) :=
  (chartYAffine R).2

end CommRing

section Field

variable (k : Type u) [Field k]

/-- The canonical point `0 = [1 : 0]` of the projective line over `k`. -/
@[stacks 01JE "zero point"]
noncomputable def zeroPoint : scheme k :=
  (zeroSection k).base (IsLocalRing.closedPoint k)

/-- A point is `0 = [1 : 0]` when it is the image of the closed point under a zero section. -/
@[stacks 01JE "zero point specification"]
def IsZeroPoint (z : scheme k) : Prop :=
  ∃ s : Spec (CommRingCat.of k) ⟶ scheme k,
    IsZeroSection k s ∧ s.base (IsLocalRing.closedPoint k) = z

/-- The canonical zero point satisfies its section-theoretic specification. -/
@[stacks 01JE "zero point specification witness"]
theorem zeroPoint_isZeroPoint : IsZeroPoint k (zeroPoint k) := by
  exact ⟨zeroSection k, zeroSection_isZeroSection k, rfl⟩

/-- The section-theoretic specification characterizes the canonical zero point. -/
@[stacks 01JE "zero point specification characterization"]
theorem isZeroPoint_iff_eq (z : scheme k) : IsZeroPoint k z ↔ z = zeroPoint k := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [(isZeroSection_iff_eq k s).mp hs]
    rfl
  · rintro rfl
    exact zeroPoint_isZeroPoint k

/-- The canonical point `∞ = [0 : 1]` of the projective line over `k`. -/
@[stacks 01JE "infinity point"]
noncomputable def infinityPoint : scheme k :=
  (infinitySection k).base (IsLocalRing.closedPoint k)

/-- A point is `∞ = [0 : 1]` when it is the image of the closed point under an infinity
section. -/
@[stacks 01JE "infinity point specification"]
def IsInfinityPoint (z : scheme k) : Prop :=
  ∃ s : Spec (CommRingCat.of k) ⟶ scheme k,
    IsInfinitySection k s ∧ s.base (IsLocalRing.closedPoint k) = z

/-- The canonical infinity point satisfies its section-theoretic specification. -/
@[stacks 01JE "infinity point specification witness"]
theorem infinityPoint_isInfinityPoint : IsInfinityPoint k (infinityPoint k) := by
  exact ⟨infinitySection k, infinitySection_isInfinitySection k, rfl⟩

/-- The section-theoretic specification characterizes the canonical infinity point. -/
@[stacks 01JE "infinity point specification characterization"]
theorem isInfinityPoint_iff_eq (z : scheme k) :
    IsInfinityPoint k z ↔ z = infinityPoint k := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [(isInfinitySection_iff_eq k s).mp hs]
    rfl
  · rintro rfl
    exact infinityPoint_isInfinityPoint k

/-- The canonical point `1 = [1 : 1]` of the projective line over `k`. -/
@[stacks 01JE "one point"]
noncomputable def onePoint : scheme k :=
  (oneSection k).base (IsLocalRing.closedPoint k)

/-- A point is `1 = [1 : 1]` when it is the image of the closed point under a one section. -/
@[stacks 01JE "one point specification"]
def IsOnePoint (z : scheme k) : Prop :=
  ∃ s : Spec (CommRingCat.of k) ⟶ scheme k,
    IsOneSection k s ∧ s.base (IsLocalRing.closedPoint k) = z

/-- The canonical one point satisfies its section-theoretic specification. -/
@[stacks 01JE "one point specification witness"]
theorem onePoint_isOnePoint : IsOnePoint k (onePoint k) := by
  exact ⟨oneSection k, oneSection_isOneSection k, rfl⟩

/-- The section-theoretic specification characterizes the canonical one point. -/
@[stacks 01JE "one point specification characterization"]
theorem isOnePoint_iff_eq (z : scheme k) : IsOnePoint k z ↔ z = onePoint k := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [(isOneSection_iff_eq k s).mp hs]
    rfl
  · rintro rfl
    exact onePoint_isOnePoint k

private theorem infinityPoint_x_mem :
    x k ∈ (infinityPoint k).asHomogeneousIdeal := by
  let q : (chartY k).toScheme :=
    (affineLineZero k ≫ (chartYIso k).inv).base
      (IsLocalRing.closedPoint k)
  let t : HomogeneousLocalization.NumDenSameDeg (grading k)
      (Submonoid.powers (y k)) :=
    ⟨1, ⟨x k, MvPolynomial.isHomogeneous_X k (0 : Fin 2)⟩,
      ⟨y k, MvPolynomial.isHomogeneous_X k (1 : Fin 2)⟩, ⟨1, by simp⟩⟩
  have hmap : affineLineZero k ≫ (chartYIso k).inv ≫
      (Proj.basicOpenIsoSpec (grading k) (y k)
        (MvPolynomial.isHomogeneous_X k (1 : Fin 2)) Nat.zero_lt_one).hom =
      Spec.map (CommRingCat.ofHom ((MvPolynomial.eval₂Hom (RingHom.id k)
        (fun _ : ULift.{u} (Fin 1) ↦ 0)).comp
        (ProjectiveSpace.CoordinateChart.dehomogenization (R := k) 1 1 Equiv.ulift.symm))) := by
    simp only [chartYIso, ProjectiveSpace.CoordinateChart.iso,
      ProjectiveSpace.CoordinateChart.isoWith, Iso.trans_inv, Iso.symm_inv,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [← Category.assoc, affineLineZero_spec k]
    simp only [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op]
    erw [← Spec.map_comp]
    rfl
  apply (ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply (grading k) q t).mp
  change HomogeneousLocalization.mk t ∈
    ((affineLineZero k ≫ (chartYIso k).inv ≫
      (Proj.basicOpenIsoSpec (grading k) (y k)
        (MvPolynomial.isHomogeneous_X k (1 : Fin 2)) Nat.zero_lt_one).hom).base
      (IsLocalRing.closedPoint k)).asIdeal
  rw [hmap]
  change ((MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : ULift.{u} (Fin 1) ↦ 0))
    (ProjectiveSpace.CoordinateChart.dehomogenization (R := k) 1 1 Equiv.ulift.symm
      (HomogeneousLocalization.mk t))) ∈ (IsLocalRing.closedPoint k).asIdeal
  have hratio : HomogeneousLocalization.mk t =
      ProjectiveSpace.affineChartHom (R := k) 1 1 Equiv.ulift.symm (MvPolynomial.X (ULift.up 0)) := by
    simp only [ProjectiveSpace.affineChartHom_X]
    apply HomogeneousLocalization.val_injective (Submonoid.powers (y k))
    simp [t, ProjectiveSpace.coordinateRatio, HomogeneousLocalization.Away.isLocalizationElem,
      HomogeneousLocalization.val_mk, HomogeneousLocalization.Away.val_mk]
  rw [hratio]
  have hd := RingHom.congr_fun
    (ProjectiveSpace.CoordinateChart.dehomogenization_comp_affineChartHom
      (R := k) 1 1 Equiv.ulift.symm) (MvPolynomial.X (ULift.up 0))
  change ProjectiveSpace.CoordinateChart.dehomogenization (R := k) 1 1 Equiv.ulift.symm
    (ProjectiveSpace.affineChartHom (R := k) 1 1 Equiv.ulift.symm
      (MvPolynomial.X (ULift.up 0))) = MvPolynomial.X (ULift.up 0) at hd
  rw [hd]
  simp

/-- Points satisfying the canonical zero and infinity specifications are distinct. -/
@[stacks 01JE "zero and infinity point distinctness"]
theorem IsZeroPoint.ne_infinity {z p : scheme k}
    (hz : IsZeroPoint k z) (hp : IsInfinityPoint k p) : z ≠ p := by
  rw [(isZeroPoint_iff_eq k z).mp hz, (isInfinityPoint_iff_eq k p).mp hp]
  intro h
  have hx : x k ∉ (zeroPoint k).asHomogeneousIdeal :=
    ((affineLineZero k ≫ (chartXIso k).inv).base (IsLocalRing.closedPoint k)).property
  rw [h] at hx
  exact hx (infinityPoint_x_mem k)

/-- The canonical zero and infinity points of the projective line are distinct. -/
@[stacks 01JE "zero and infinity points are distinct"]
theorem zeroPoint_ne_infinityPoint : zeroPoint k ≠ infinityPoint k :=
  (zeroPoint_isZeroPoint k).ne_infinity k (infinityPoint_isInfinityPoint k)

/-- The projective line over a field is not affine. -/
@[stacks 01JE "not affine"]
theorem not_isAffine : ¬ IsAffine (scheme k) := by
  intro h
  letI := h
  haveI : IsIso ((toSpec k).appTop) := by
    apply (isIso_comp_left_iff (Scheme.ΓSpecIso (CommRingCat.of k)).inv _).mp
    exact ProjectiveSpace.globalSectionsComparison.isIso k 1
  haveI : IsIso (toSpec k ≫ (Spec (CommRingCat.of k)).isoSpec.hom) := by
    rw [← Scheme.isoSpec_hom_naturality]
    infer_instance
  haveI : IsIso (toSpec k) := IsIso.of_isIso_comp_right
    (toSpec k) (Spec (CommRingCat.of k)).isoSpec.hom
  apply zeroPoint_ne_infinityPoint k
  apply (toSpec k).isOpenEmbedding.injective
  exact Subsingleton.elim _ _

/-- The projective line over a field has infinitely many points. -/
@[stacks 01JE "projective-line points are infinite"]
instance infinite : Infinite (scheme k) := by
  haveI : Infinite (PrimeSpectrum (Polynomial k)) := by
    by_contra h
    haveI : Finite (PrimeSpectrum (Polynomial k)) := not_infinite_iff_finite.mp h
    have hmax : (⊥ : Ideal (Polynomial k)).IsMaximal :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal ⟨⊥, Ideal.isPrime_bot⟩).mp
        isClosed_singleton
    exact Polynomial.not_isField k (Ring.isField_iff_maximal_bot.mpr hmax)
  let e : affineLine k ≅ Spec (CommRingCat.of (Polynomial k)) :=
    AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k) ≪≫
      Scheme.Spec.mapIso
        (MvPolynomial.uniqueAlgEquiv k (ULift.{u} (Fin 1))).toRingEquiv.toCommRingCatIso.op.symm
  let f : Spec (CommRingCat.of (Polynomial k)) ⟶ scheme k :=
    e.inv ≫ (chartXIso k).inv ≫ (chartX k).ι
  haveI : Infinite (Spec (CommRingCat.of (Polynomial k))) :=
    ‹Infinite (PrimeSpectrum (Polynomial k))›
  exact Infinite.of_injective f f.isOpenEmbedding.injective

end Field

end AlgebraicGeometry.ProjectiveLine
