/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.AwayOne
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Chart
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restricting the coordinate on the complement of one

This file compares the affine coordinate on `D₊(Y - X)` with the coordinates on the two
standard charts of the projective line. The comparison equations are written without division,
so they remain valid over an arbitrary commutative ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLine

variable (R : Type u) [CommRing R]

namespace AwayOne

namespace Part

/-- The homogeneous polynomial `(Y - X)Tᵢ` defining the part of `D₊(Y - X)` in the `i`-th
standard chart. -/
@[stacks 01JE "product equation for a complement-of-one chart part"]
abbrev polynomial (i : Fin 2) : MvPolynomial (Fin 2) R :=
  (y R - x R) * ProjectiveLine.coordinate R i

/-- The product polynomial `(Y - X)Tᵢ` has degree two. -/
@[stacks 01JE "degree of a complement-of-one chart-part equation"]
theorem polynomial_mem_grading_two (i : Fin 2) : polynomial R i ∈ grading R 2 := sorry

/-- The part of `D₊(Y - X)` in the `i`-th standard chart. -/
@[stacks 01JE "complement-of-one chart part"]
abbrev partOpen (i : Fin 2) : (scheme R).Opens :=
  ProjectiveSpace.basicOpen (R := R) 1 (polynomial R i)

/-- The indexed chart part is the intersection of `D₊(Y - X)` with the `i`-th standard chart. -/
@[simp, stacks 01JE "complement-of-one chart-part intersection"]
theorem partOpen_eq (i : Fin 2) :
    partOpen R i =
      awayOne R ⊓ (ProjectiveSpace.coordinateBasicOpen (R := R) 1 i : (scheme R).Opens) := sorry

/-- The degree-zero homogeneous localization representing sections on the `i`-th chart part. -/
@[stacks 01JE "complement-of-one chart-part ring"]
abbrev ring (i : Fin 2) := HomogeneousLocalization.Away (grading R) (polynomial R i)

/-- The canonical homogeneous-localization identification of the `i`-th chart-part section ring. -/
@[stacks 01JE "complement-of-one chart-part sections isomorphism"]
noncomputable def sectionsIso (i : Fin 2) :
    CommRingCat.of (ring R i) ≅ Γ(scheme R, partOpen R i) :=
  Proj.basicOpenIsoAway (grading R) (polynomial R i)
    (SetLike.mul_mem_graded
      (sub_mem
        (MvPolynomial.isHomogeneous_X R (1 : Fin 2))
        (MvPolynomial.isHomogeneous_X R (0 : Fin 2)))
      (MvPolynomial.isHomogeneous_X R i))
    (Nat.zero_lt_succ 1)

/-- The forward map of the canonical `i`-th chart-part section-ring identification. -/
@[stacks 01JE "complement-of-one chart-part sections comparison"]
noncomputable abbrev sectionsComparison (i : Fin 2) :
    CommRingCat.of (ring R i) ⟶ Γ(scheme R, partOpen R i) :=
  (sectionsIso R i).hom

/-- The canonical chart-part comparison agrees with Mathlib's `Proj.awayToSection` map. -/
@[simp, stacks 01JE "complement-of-one chart-part comparison readout"]
theorem sectionsComparison_eq_awayToSection (i : Fin 2) :
    sectionsComparison R i = Proj.awayToSection (grading R) (polynomial R i) := sorry

/-- Localization from the ring of `D₊(Y - X)` to the ring of its `i`-th chart part, as an
algebra homomorphism over the degree-zero part of the homogeneous coordinate ring. -/
@[stacks 01JE "restrict complement-of-one sections to a chart part"]
noncomputable def fromAwayOneAlgHom (i : Fin 2) :
    AwayOne.ring R →ₐ[grading R 0] ring R i :=
  HomogeneousLocalization.awayMapₐ (grading R)
    (f := y R - x R) (g := ProjectiveLine.coordinate R i) (x := polynomial R i)
    (MvPolynomial.isHomogeneous_X R i) rfl

/-- The ring-hom view of localization from `D₊(Y - X)` to its `i`-th chart part. -/
@[stacks 01JE "restriction to a complement-of-one chart part"]
noncomputable abbrev fromAwayOne (i : Fin 2) : AwayOne.ring R →+* ring R i :=
  (fromAwayOneAlgHom R i).toRingHom

/-- The chart-part localization ring map is the underlying map of its algebra-hom owner. -/
@[simp, stacks 01JE "chart-part localization algebra-map bridge"]
theorem fromAwayOneAlgHom_toRingHom (i : Fin 2) :
    (fromAwayOneAlgHom R i).toRingHom = fromAwayOne R i := sorry

/-- Restriction of sections on `D₊(Y - X)` to its part in the `i`-th standard chart. -/
@[stacks 01JE "restrict complement-of-one sections to a chart part"]
noncomputable def restrict (i : Fin 2) :
    Γ(scheme R, awayOne R) ⟶ Γ(scheme R, partOpen R i) :=
  (scheme R).presheaf.map
    (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left
      (grading R) (y R - x R) (ProjectiveLine.coordinate R i))).op

/-- Localization from the `i`-th standard chart ring to the corresponding chart part, as an
algebra homomorphism over the degree-zero part of the homogeneous coordinate ring. -/
@[stacks 01JE "restrict a standard chart to a complement-of-one part"]
noncomputable def fromChartAlgHom (i : Fin 2) :
    ProjectiveSpace.coordinateAway (R := R) 1 i →ₐ[grading R 0] ring R i :=
  HomogeneousLocalization.awayMapₐ (grading R)
    (f := ProjectiveLine.coordinate R i) (g := y R - x R) (x := polynomial R i)
    (sub_mem
      (MvPolynomial.isHomogeneous_X R (1 : Fin 2))
      (MvPolynomial.isHomogeneous_X R (0 : Fin 2)))
    (mul_comm (y R - x R) (ProjectiveLine.coordinate R i))

/-- The ring-hom view of localization from the `i`-th standard chart to its chart part. -/
@[stacks 01JE "standard-chart restriction to a complement-of-one part"]
noncomputable abbrev fromChart (i : Fin 2) :
    ProjectiveSpace.coordinateAway (R := R) 1 i →+* ring R i :=
  (fromChartAlgHom R i).toRingHom

/-- The standard-chart localization ring map is the underlying map of its algebra-hom owner. -/
@[simp, stacks 01JE "standard-chart localization algebra-map bridge"]
theorem fromChartAlgHom_toRingHom (i : Fin 2) :
    (fromChartAlgHom R i).toRingHom = fromChart R i := sorry

/-- Homogeneous localization and sheaf restriction agree on every indexed chart part. -/
@[reassoc, stacks 01JE "complement-of-one indexed restriction compatibility"]
theorem fromAwayOne_sectionsComparison (i : Fin 2) :
    CommRingCat.ofHom (fromAwayOne R i) ≫ sectionsComparison R i =
      AwayOne.ringSectionsComparison R ≫ restrict R i := sorry

/-- Restriction of sections from the `i`-th standard chart to its indexed chart part. -/
@[stacks 01JE "restrict a standard chart to a complement-of-one chart part"]
noncomputable def restrictChart (i : Fin 2) :
    CommRingCat.of (ProjectiveSpace.coordinateAway (R := R) 1 i) ⟶
      Γ(scheme R, partOpen R i) :=
  (ProjectiveSpace.coordinateBasicOpenIsoAway (R := R) 1 i).hom ≫
    (scheme R).presheaf.map
      (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_right
        (grading R) (y R - x R) (ProjectiveLine.coordinate R i))).op

/-- The indexed chart restriction is homogeneous localization followed by the part sections
comparison. -/
@[reassoc, stacks 01JE "indexed chart restriction comparison"]
theorem fromChart_sectionsComparison (i : Fin 2) :
    restrictChart R i =
      CommRingCat.ofHom (fromChart R i) ≫ sectionsComparison R i := sorry

end Part

namespace XPart

/-- The homogeneous polynomial `(Y - X)X` defining the part of `D₊(Y - X)` in the `X`-chart. -/
@[stacks 01JE "equation for the complement of one in the X-chart"]
abbrev polynomial : MvPolynomial (Fin 2) R := Part.polynomial R 0

end XPart

namespace YPart

/-- The homogeneous polynomial `(Y - X)Y` defining the part of `D₊(Y - X)` in the `Y`-chart. -/
@[stacks 01JE "equation for the complement of one in the Y-chart"]
abbrev polynomial : MvPolynomial (Fin 2) R := Part.polynomial R 1

end YPart

/-- The part of `D₊(Y - X)` lying in the standard `X`-chart, presented as the projective basic
open `D₊((Y - X)X)`. -/
@[stacks 01JE "complement of one in the X-chart"]
abbrev xPart : (scheme R).Opens :=
  Part.partOpen R 0

/-- The part of `D₊(Y - X)` lying in the standard `Y`-chart, presented as the projective basic
open `D₊((Y - X)Y)`. -/
@[stacks 01JE "complement of one in the Y-chart"]
abbrev yPart : (scheme R).Opens :=
  Part.partOpen R 1

/-- The product basic-open presentation of the `X`-part agrees with the corresponding
intersection. -/
@[simp, stacks 01JE "complement-of-one X-part intersection"]
theorem xPart_eq : xPart R = awayOne R ⊓ chartX R := sorry

/-- The product basic-open presentation of the `Y`-part agrees with the corresponding
intersection. -/
@[simp, stacks 01JE "complement-of-one Y-part intersection"]
theorem yPart_eq : yPart R = awayOne R ⊓ chartY R := sorry

/-- Restriction of sections on `D₊(Y - X)` to its part in the `X`-chart. -/
@[stacks 01JE "restrict complement-of-one sections to the X-chart"]
noncomputable abbrev restrictX :
    Γ(scheme R, awayOne R) ⟶ Γ(scheme R, xPart R) :=
  Part.restrict R 0

/-- Restriction of sections on `D₊(Y - X)` to its part in the `Y`-chart. -/
@[stacks 01JE "restrict complement-of-one sections to the Y-chart"]
noncomputable abbrev restrictY :
    Γ(scheme R, awayOne R) ⟶ Γ(scheme R, yPart R) :=
  Part.restrict R 1

namespace XPart

/-- The degree-zero homogeneous localization representing sections on `D₊((Y - X)X)`. -/
@[stacks 01JE "complement-of-one X-part ring"]
abbrev ring := Part.ring R 0

/-- The canonical homogeneous-localization identification of the `X`-part section ring. -/
@[stacks 01JE "complement-of-one X-part sections isomorphism"]
noncomputable abbrev sectionsIso : CommRingCat.of (ring R) ≅ Γ(scheme R, xPart R) :=
  Part.sectionsIso R 0

/-- The forward map of the canonical `X`-part sections isomorphism. -/
@[stacks 01JE "complement-of-one X-part sections comparison"]
noncomputable abbrev sectionsComparison :
    CommRingCat.of (ring R) ⟶ Γ(scheme R, xPart R) :=
  Part.sectionsComparison R 0

/-- Localization from the ring of `D₊(Y - X)` to the ring of `D₊((Y - X)X)`, as an
algebra homomorphism over the degree-zero homogeneous coordinate ring. -/
@[stacks 01JE "restrict the complement of one to its X-part algebraically"]
noncomputable abbrev fromAwayOneAlgHom : AwayOne.ring R →ₐ[grading R 0] ring R :=
  Part.fromAwayOneAlgHom R 0

/-- The ring-hom view of localization from `D₊(Y - X)` to its `X`-part. -/
@[stacks 01JE "restrict the complement of one to its X-part"]
noncomputable abbrev fromAwayOne : AwayOne.ring R →+* ring R :=
  (fromAwayOneAlgHom R).toRingHom

/-- The specialized `X`-part ring map is the underlying map of its algebra-hom owner. -/
@[simp, stacks 01JE "X-part restriction algebra/ring bridge"]
theorem fromAwayOneAlgHom_toRingHom :
    (fromAwayOneAlgHom R).toRingHom = fromAwayOne R := sorry

/-- Localization from the `X`-chart ring to the ring of `D₊((Y - X)X)`, as an algebra
homomorphism over the degree-zero homogeneous coordinate ring. -/
@[stacks 01JE "restrict the X-chart to the complement of one algebraically"]
noncomputable abbrev fromXChartAlgHom : XChart.ring R →ₐ[grading R 0] ring R :=
  Part.fromChartAlgHom R 0

/-- The ring-hom view of localization from the `X`-chart to the complement of one. -/
@[stacks 01JE "restrict the X-chart to the complement of one"]
noncomputable abbrev fromXChart : XChart.ring R →+* ring R :=
  (fromXChartAlgHom R).toRingHom

/-- The specialized `X`-chart ring map is the underlying map of its algebra-hom owner. -/
@[simp, stacks 01JE "X-chart restriction algebra/ring bridge"]
theorem fromXChartAlgHom_toRingHom :
    (fromXChartAlgHom R).toRingHom = fromXChart R := sorry

/-- The two affine coordinates satisfy `(Y / X - 1) * (X / (Y - X)) = 1` in the explicit
homogeneous-localization ring of the `X`-part. -/
@[stacks 01JE "complement-of-one coordinate relation on the X-part"]
theorem coordinate_relation :
    (fromXChart R (XChart.coordinate R) - 1) *
        fromAwayOne R (AwayOne.coordinate R) = 1 := sorry

/-- Homogeneous localization and sheaf restriction from `D₊(Y - X)` agree on the `X`-part. -/
@[stacks 01JE "complement-of-one restriction compatibility on the X-part"]
theorem fromAwayOne_sectionsComparison :
    CommRingCat.ofHom (fromAwayOne R) ≫ sectionsComparison R =
      AwayOne.ringSectionsComparison R ≫ restrictX R := sorry

end XPart

namespace YPart

/-- The degree-zero homogeneous localization representing sections on `D₊((Y - X)Y)`. -/
@[stacks 01JE "complement-of-one Y-part ring"]
abbrev ring := Part.ring R 1

/-- The canonical homogeneous-localization identification of the `Y`-part section ring. -/
@[stacks 01JE "complement-of-one Y-part sections isomorphism"]
noncomputable abbrev sectionsIso : CommRingCat.of (ring R) ≅ Γ(scheme R, yPart R) :=
  Part.sectionsIso R 1

/-- The forward map of the canonical `Y`-part sections isomorphism. -/
@[stacks 01JE "complement-of-one Y-part sections comparison"]
noncomputable abbrev sectionsComparison :
    CommRingCat.of (ring R) ⟶ Γ(scheme R, yPart R) :=
  Part.sectionsComparison R 1

/-- Localization from the ring of `D₊(Y - X)` to the ring of `D₊((Y - X)Y)`, as an
algebra homomorphism over the degree-zero homogeneous coordinate ring. -/
@[stacks 01JE "restrict the complement of one to its Y-part algebraically"]
noncomputable abbrev fromAwayOneAlgHom : AwayOne.ring R →ₐ[grading R 0] ring R :=
  Part.fromAwayOneAlgHom R 1

/-- The ring-hom view of localization from `D₊(Y - X)` to its `Y`-part. -/
@[stacks 01JE "restrict the complement of one to its Y-part"]
noncomputable abbrev fromAwayOne : AwayOne.ring R →+* ring R :=
  (fromAwayOneAlgHom R).toRingHom

/-- The specialized `Y`-part ring map is the underlying map of its algebra-hom owner. -/
@[simp, stacks 01JE "Y-part restriction algebra/ring bridge"]
theorem fromAwayOneAlgHom_toRingHom :
    (fromAwayOneAlgHom R).toRingHom = fromAwayOne R := sorry

/-- Localization from the `Y`-chart ring to the ring of `D₊((Y - X)Y)`, as an algebra
homomorphism over the degree-zero homogeneous coordinate ring. -/
@[stacks 01JE "restrict the Y-chart to the complement of one algebraically"]
noncomputable abbrev fromYChartAlgHom : YChart.ring R →ₐ[grading R 0] ring R :=
  Part.fromChartAlgHom R 1

/-- The ring-hom view of localization from the `Y`-chart to the complement of one. -/
@[stacks 01JE "restrict the Y-chart to the complement of one"]
noncomputable abbrev fromYChart : YChart.ring R →+* ring R :=
  (fromYChartAlgHom R).toRingHom

/-- The specialized `Y`-chart ring map is the underlying map of its algebra-hom owner. -/
@[simp, stacks 01JE "Y-chart restriction algebra/ring bridge"]
theorem fromYChartAlgHom_toRingHom :
    (fromYChartAlgHom R).toRingHom = fromYChart R := sorry

/-- The two affine coordinates satisfy `(1 - X / Y) * (X / (Y - X)) = X / Y` in the explicit
homogeneous-localization ring of the `Y`-part. -/
@[stacks 01JE "complement-of-one coordinate relation on the Y-part"]
theorem coordinate_relation :
    (1 - fromYChart R (YChart.coordinate R)) *
        fromAwayOne R (AwayOne.coordinate R) =
      fromYChart R (YChart.coordinate R) := sorry

/-- Homogeneous localization and sheaf restriction from `D₊(Y - X)` agree on the `Y`-part. -/
@[stacks 01JE "complement-of-one restriction compatibility on the Y-part"]
theorem fromAwayOne_sectionsComparison :
    CommRingCat.ofHom (fromAwayOne R) ≫ sectionsComparison R =
      AwayOne.ringSectionsComparison R ≫ restrictY R := sorry

end YPart

end AwayOne

namespace XChart

/-- Restriction from the homogeneous-localization presentation of the `X`-chart ring to the
part of that chart contained in `D₊(Y - X)`. -/
@[stacks 01JE "restrict the X-chart to the complement of one"]
noncomputable abbrev restrictAwayOne :
    CommRingCat.of (ring R) ⟶ Γ(scheme R, AwayOne.xPart R) :=
  AwayOne.Part.restrictChart R 0

/-- Homogeneous localization and sheaf restriction from the `X`-chart agree on its part in
`D₊(Y - X)`. -/
@[stacks 01JE "X-chart restriction compatibility away from one"]
theorem restrictAwayOne_eq :
    restrictAwayOne R =
      CommRingCat.ofHom (AwayOne.XPart.fromXChart R) ≫
        AwayOne.XPart.sectionsComparison R := sorry

end XChart

namespace YChart

/-- Restriction from the homogeneous-localization presentation of the `Y`-chart ring to the
part of that chart contained in `D₊(Y - X)`. -/
@[stacks 01JE "restrict the Y-chart to the complement of one"]
noncomputable abbrev restrictAwayOne :
    CommRingCat.of (ring R) ⟶ Γ(scheme R, AwayOne.yPart R) :=
  AwayOne.Part.restrictChart R 1

/-- Homogeneous localization and sheaf restriction from the `Y`-chart agree on its part in
`D₊(Y - X)`. -/
@[stacks 01JE "Y-chart restriction compatibility away from one"]
theorem restrictAwayOne_eq :
    restrictAwayOne R =
      CommRingCat.ofHom (AwayOne.YPart.fromYChart R) ≫
        AwayOne.YPart.sectionsComparison R := sorry

end YChart

/-- On the `X`-part of `D₊(Y - X)`, the section `s = X / (Y - X)` satisfies
`(Y / X - 1) * s = 1`. -/
@[stacks 01JE "complement-of-one coordinate on the X-chart"]
theorem AwayOne.coordinateSection_restrictX :
    ((XChart.restrictAwayOne R).hom (XChart.coordinate R) - 1) *
        (AwayOne.restrictX R).hom (AwayOne.coordinateSection R) = 1 := sorry

/-- On the `Y`-part of `D₊(Y - X)`, the section `s = X / (Y - X)` satisfies
`(1 - X / Y) * s = X / Y`. -/
@[stacks 01JE "complement-of-one coordinate on the Y-chart"]
theorem AwayOne.coordinateSection_restrictY :
    (1 - (YChart.restrictAwayOne R).hom (YChart.coordinate R)) *
        (AwayOne.restrictY R).hom (AwayOne.coordinateSection R) =
      (YChart.restrictAwayOne R).hom (YChart.coordinate R) := sorry

end AlgebraicGeometry.ProjectiveLine
