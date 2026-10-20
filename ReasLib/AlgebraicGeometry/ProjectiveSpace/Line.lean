/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Coordinate
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
theorem toSpec_isSeparated : IsSeparated (toSpec R) := sorry

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

/-- The zero section of the affine-line model. -/
@[stacks 01JE "affine-line zero section"]
noncomputable def affineLineZero : Spec (CommRingCat.of R) ⟶ affineLine R :=
  AffineSpace.homOfVector (𝟙 _) (fun _ ↦ 0)

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
theorem zeroSection_isZeroSection : IsZeroSection R (zeroSection R) := sorry

/-- The `X`-chart specification characterizes the canonical zero section. -/
@[stacks 01JE "zero section specification characterization"]
theorem isZeroSection_iff_eq (s : Spec (CommRingCat.of R) ⟶ scheme R) :
    IsZeroSection R s ↔ s = zeroSection R := sorry

/-- A zero section is a section of the projective-line structure morphism. -/
@[stacks 01JE "zero section over the base"]
theorem IsZeroSection.toSpec {s : Spec (CommRingCat.of R) ⟶ scheme R}
    (hs : IsZeroSection R s) : s ≫ toSpec R = 𝟙 _ := sorry

/-- The canonical zero section splits the projective-line structure morphism. -/
@[simp, stacks 01JE "zero section structure map"]
theorem zeroSection_toSpec : zeroSection R ≫ toSpec R = 𝟙 _ := sorry

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
    IsInfinitySection R (infinitySection R) := sorry

/-- The `Y`-chart specification characterizes the canonical infinity section. -/
@[stacks 01JE "infinity section specification characterization"]
theorem isInfinitySection_iff_eq (s : Spec (CommRingCat.of R) ⟶ scheme R) :
    IsInfinitySection R s ↔ s = infinitySection R := sorry

/-- An infinity section is a section of the projective-line structure morphism. -/
@[stacks 01JE "infinity section over the base"]
theorem IsInfinitySection.toSpec {s : Spec (CommRingCat.of R) ⟶ scheme R}
    (hs : IsInfinitySection R s) : s ≫ toSpec R = 𝟙 _ := sorry

/-- The canonical infinity section splits the projective-line structure morphism. -/
@[simp, stacks 01JE "infinity section structure map"]
theorem infinitySection_toSpec : infinitySection R ≫ toSpec R = 𝟙 _ := sorry

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
theorem oneSection_isOneSection : IsOneSection R (oneSection R) := sorry

/-- The `X`-chart specification characterizes the canonical one section. -/
@[stacks 01JE "one section specification characterization"]
theorem isOneSection_iff_eq (s : Spec (CommRingCat.of R) ⟶ scheme R) :
    IsOneSection R s ↔ s = oneSection R := sorry

/-- A one section is a section of the projective-line structure morphism. -/
@[stacks 01JE "one section over the base"]
theorem IsOneSection.toSpec {s : Spec (CommRingCat.of R) ⟶ scheme R}
    (hs : IsOneSection R s) : s ≫ toSpec R = 𝟙 _ := sorry

/-- The canonical one section splits the projective-line structure morphism. -/
@[simp, stacks 01JE "one section structure map"]
theorem oneSection_toSpec : oneSection R ≫ toSpec R = 𝟙 _ := sorry

/-- The two standard affine charts cover the projective line. -/
@[stacks 01JE "standard affine cover"]
theorem charts_cover : chartX R ⊔ chartY R = ⊤ := sorry

/-- The standard chart `D₊(X)` is affine. -/
@[stacks 01JE "projective-line X chart affineness"]
theorem chartX_isAffineOpen : IsAffineOpen (chartX R) := sorry

/-- The standard chart `D₊(Y)` is affine. -/
@[stacks 01JE "projective-line Y chart affineness"]
theorem chartY_isAffineOpen : IsAffineOpen (chartY R) := sorry

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
theorem zeroPoint_isZeroPoint : IsZeroPoint k (zeroPoint k) := sorry

/-- The section-theoretic specification characterizes the canonical zero point. -/
@[stacks 01JE "zero point specification characterization"]
theorem isZeroPoint_iff_eq (z : scheme k) : IsZeroPoint k z ↔ z = zeroPoint k := sorry

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
theorem infinityPoint_isInfinityPoint : IsInfinityPoint k (infinityPoint k) := sorry

/-- The section-theoretic specification characterizes the canonical infinity point. -/
@[stacks 01JE "infinity point specification characterization"]
theorem isInfinityPoint_iff_eq (z : scheme k) :
    IsInfinityPoint k z ↔ z = infinityPoint k := sorry

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
theorem onePoint_isOnePoint : IsOnePoint k (onePoint k) := sorry

/-- The section-theoretic specification characterizes the canonical one point. -/
@[stacks 01JE "one point specification characterization"]
theorem isOnePoint_iff_eq (z : scheme k) : IsOnePoint k z ↔ z = onePoint k := sorry

/-- Points satisfying the canonical zero and infinity specifications are distinct. -/
@[stacks 01JE "zero and infinity point distinctness"]
theorem IsZeroPoint.ne_infinity {z p : scheme k}
    (hz : IsZeroPoint k z) (hp : IsInfinityPoint k p) : z ≠ p := sorry

/-- The canonical zero and infinity points of the projective line are distinct. -/
@[stacks 01JE "zero and infinity points are distinct"]
theorem zeroPoint_ne_infinityPoint : zeroPoint k ≠ infinityPoint k := sorry

/-- The projective line over a field is not affine. -/
@[stacks 01JE "not affine"]
theorem not_isAffine : ¬ IsAffine (scheme k) := sorry

/-- The projective line over a field has infinitely many points. -/
@[stacks 01JE "projective-line points are infinite"]
instance infinite : Infinite (scheme k) := sorry

end Field

end AlgebraicGeometry.ProjectiveLine
