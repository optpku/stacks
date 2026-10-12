/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Gluing
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Chart
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Overlap
import Mathlib.Tactic.CrossRefAttribute

/-!
# The standard gluing presentation of the projective line

This file packages the two standard coordinate charts as an open cover and uses Mathlib's
canonical `OpenCover.gluedCover` construction to recover the projective line.  It also exposes the
two chart-ring restriction maps to the common overlap.  Their distinguished coordinates map to
the two homogeneous-localization coordinates whose product is one, which is the formal transition
law corresponding to `x = y⁻¹`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLine

variable (R : Type u) [CommRing R]

/-- The two standard opens `D₊(X)` and `D₊(Y)`, indexed in that order. -/
@[stacks 01JE "standard projective-line indexed opens"]
def standardOpens : Fin 2 → (scheme R).Opens :=
  fun i ↦ (ProjectiveSpace.coordinateBasicOpen (R := R) 1 i : (scheme R).Opens)

/-- The zeroth member of the standard two-chart family is `D₊(X)`. -/
@[simp, stacks 01JE "standard projective-line X chart"]
theorem standardOpens_zero : standardOpens R 0 = chartX R := sorry

/-- The first member of the standard two-chart family is `D₊(Y)`. -/
@[simp, stacks 01JE "standard projective-line Y chart"]
theorem standardOpens_one : standardOpens R 1 = chartY R := sorry

/-- The standard two-chart family is an open cover of the projective line. -/
@[stacks 01JE "standard projective-line cover"]
theorem standardOpens_isOpenCover :
    TopologicalSpace.IsOpenCover (standardOpens R) := sorry

/- The scheme gluing construction requires its index universe to match the scheme universe. -/
/-- The standard two-chart family with the universe-lifted index used by `Scheme.GlueData`. -/
@[stacks 01JE "universe-lifted standard projective-line opens"]
def standardOpensLift : ULift.{u} (Fin 2) → (scheme R).Opens :=
  fun i ↦ standardOpens R i.down

/-- The universe-lifted standard family is still an open cover. -/
@[stacks 01JE "universe-lifted standard projective-line cover"]
theorem standardOpensLift_isOpenCover :
    TopologicalSpace.IsOpenCover (standardOpensLift R) := sorry

/-- The standard two-chart cover of the projective line as a bundled scheme open cover. -/
@[stacks 01JE "standard projective-line open cover"]
def standardCover : (scheme R).OpenCover :=
  (scheme R).openCoverOfIsOpenCover (standardOpensLift R)
    (standardOpensLift_isOpenCover R)

/-- The canonical gluing datum associated with the two standard projective-line charts. -/
@[stacks 01JE "standard projective-line gluing datum"]
noncomputable abbrev glueData (R : Type u) [CommRing R] : Scheme.GlueData :=
  (standardCover R).gluedCover

/-- The canonical morphism from the scheme glued from the two standard charts to the projective
line. -/
@[stacks 01JE "standard projective-line gluing comparison"]
noncomputable abbrev fromGlued (R : Type u) [CommRing R] : (glueData R).glued ⟶ scheme R :=
  (standardCover R).fromGlued

/-- The concrete isomorphism from the canonically glued standard cover to the projective line. -/
@[stacks 01JE "standard projective-line gluing isomorphism"]
noncomputable abbrev gluedIso (R : Type u) [CommRing R] : (glueData R).glued ≅ scheme R :=
  asIso (fromGlued R)

/-- On each chart, the gluing comparison is the corresponding open immersion into the projective
line. -/
@[reassoc, stacks 01JE "standard projective-line gluing chart"]
theorem ι_fromGlued (i : ULift.{u} (Fin 2)) :
    (glueData R).ι i ≫ fromGlued R = (standardCover R).f i := sorry

/-- The common overlap lies in the `X`-chart. -/
@[stacks 01JE "projective-line overlap in the X chart"]
theorem overlap_le_chartX : overlap R ≤ chartX R := sorry

/-- The common overlap lies in the `Y`-chart. -/
@[stacks 01JE "projective-line overlap in the Y chart"]
theorem overlap_le_chartY : overlap R ≤ chartY R := sorry

namespace XChart

/-- The restriction from the `X`-chart to the common overlap, retaining its natural algebra
homomorphism over the degree-zero homogeneous coordinate ring. -/
@[stacks 01JE "projective-line X-chart overlap restriction algebra map"]
noncomputable def toOverlapAlgHom :
    ring R →ₐ[grading R 0] Overlap.ring R :=
  HomogeneousLocalization.awayMapₐ (grading R)
    (f := x R) (g := y R) (x := x R * y R)
    (MvPolynomial.isHomogeneous_X R (1 : Fin 2)) rfl

/-- Restriction from the `X`-chart ring to the homogeneous-localization ring of the common
overlap. -/
@[stacks 01JE "projective-line X-chart overlap restriction"]
noncomputable abbrev toOverlap : ring R →+* Overlap.ring R :=
  (toOverlapAlgHom R).toRingHom

/-- The ring-hom presentation of the `X`-chart restriction is induced by its algebra-hom owner. -/
@[simp, stacks 01JE "projective-line X-chart restriction algebra-map bridge"]
theorem toOverlapAlgHom_toRingHom :
    (toOverlapAlgHom R).toRingHom = toOverlap R := sorry

/-- Restriction sends `Y / X` to the corresponding coordinate on the common overlap. -/
@[simp, stacks 01JE "X-chart coordinate on the overlap"]
theorem toOverlap_coordinate :
    toOverlap R (coordinate R) = Overlap.xChartCoordinate R := sorry

/-- The actual restriction of functions from the `X`-chart to the common overlap, expressed from
the canonical homogeneous-localization presentation of the chart ring. -/
@[stacks 01JE "X-chart sections restriction to the overlap"]
noncomputable def sectionsRestriction :
    CommRingCat.of (ring R) ⟶ Γ(scheme R, overlap R) :=
  sectionsComparison R ≫
    (scheme R).presheaf.map
      (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_left
        (grading R) (x R) (y R))).op

/-- The sheaf-theoretic restriction from the `X`-chart agrees with homogeneous localization
followed by the common-overlap sections comparison. -/
@[stacks 01JE "X-chart overlap restriction comparison"]
theorem sectionsRestriction_eq :
    sectionsRestriction R =
      CommRingCat.ofHom (toOverlap R) ≫ Overlap.sectionsComparison R := sorry

/-- The restricted `X`-chart coordinate is the common-overlap coordinate `Y / X`. -/
@[simp, stacks 01JE "X-chart restricted coordinate"]
theorem sectionsRestriction_coordinate :
    (sectionsRestriction R).hom (coordinate R) =
      (Overlap.sectionsComparison R).hom (Overlap.xChartCoordinate R) := sorry

end XChart

namespace YChart

/-- The restriction from the `Y`-chart to the common overlap, retaining its natural algebra
homomorphism over the degree-zero homogeneous coordinate ring. -/
@[stacks 01JE "projective-line Y-chart overlap restriction algebra map"]
noncomputable def toOverlapAlgHom :
    ring R →ₐ[grading R 0] Overlap.ring R :=
  HomogeneousLocalization.awayMapₐ (grading R)
    (f := y R) (g := x R) (x := x R * y R)
    (MvPolynomial.isHomogeneous_X R (0 : Fin 2)) (mul_comm (x R) (y R))

/-- Restriction from the `Y`-chart ring to the homogeneous-localization ring of the common
overlap. -/
@[stacks 01JE "projective-line Y-chart overlap restriction"]
noncomputable abbrev toOverlap : ring R →+* Overlap.ring R :=
  (toOverlapAlgHom R).toRingHom

/-- The ring-hom presentation of the `Y`-chart restriction is induced by its algebra-hom owner. -/
@[simp, stacks 01JE "projective-line Y-chart restriction algebra-map bridge"]
theorem toOverlapAlgHom_toRingHom :
    (toOverlapAlgHom R).toRingHom = toOverlap R := sorry

/-- Restriction sends `X / Y` to the corresponding coordinate on the common overlap. -/
@[simp, stacks 01JE "Y-chart coordinate on the overlap"]
theorem toOverlap_coordinate :
    toOverlap R (coordinate R) = Overlap.yChartCoordinate R := sorry

/-- The actual restriction of functions from the `Y`-chart to the common overlap, expressed from
the canonical homogeneous-localization presentation of the chart ring. -/
@[stacks 01JE "Y-chart sections restriction to the overlap"]
noncomputable def sectionsRestriction :
    CommRingCat.of (ring R) ⟶ Γ(scheme R, overlap R) :=
  sectionsComparison R ≫
    (scheme R).presheaf.map
      (homOfLE (ProjectiveSpectrum.basicOpen_mul_le_right
        (grading R) (x R) (y R))).op

/-- The sheaf-theoretic restriction from the `Y`-chart agrees with homogeneous localization
followed by the common-overlap sections comparison. -/
@[stacks 01JE "Y-chart overlap restriction comparison"]
theorem sectionsRestriction_eq :
    sectionsRestriction R =
      CommRingCat.ofHom (toOverlap R) ≫ Overlap.sectionsComparison R := sorry

/-- The restricted `Y`-chart coordinate is the common-overlap coordinate `X / Y`. -/
@[simp, stacks 01JE "Y-chart restricted coordinate"]
theorem sectionsRestriction_coordinate :
    (sectionsRestriction R).hom (coordinate R) =
      (Overlap.sectionsComparison R).hom (Overlap.yChartCoordinate R) := sorry

end YChart

/-- On the common overlap, the restrictions of the two affine chart coordinates multiply to one.
This is the coordinate-ring form of the transition law `x = y⁻¹`. -/
@[simp, stacks 01JE "projective-line chart transition by inversion"]
theorem restrictedCoordinates_mul :
    (XChart.sectionsRestriction R).hom (XChart.coordinate R) *
        (YChart.sectionsRestriction R).hom (YChart.coordinate R) = 1 := sorry

end AlgebraicGeometry.ProjectiveLine
