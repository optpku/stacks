/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.AwayOne.Restriction
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Gluing

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveLine

variable (k : Type u) [Field k]

/- Example 26.14.4 (Projective line): the canonical projective line, its standard affine cover and
inverse transition coordinates, the affine complement `D₊(Y - X)`, its global sections, and its
nonaffineness. Its standard sections and the points `0`, `∞`, and `1` are explicit data; chart
identifications and their inverses are carried by explicit chart isomorphisms, while the standard
two-chart gluing is the canonical gluing attached to this open cover. -/
@[stacks 01JE "projective line"] #check scheme k
#check toSpec k
@[stacks 01JE "distinguished sections"]
#check zeroSection k
#check infinitySection k
#check oneSection k
#check zeroSection_toSpec k
#check infinitySection_toSpec k
#check oneSection_toSpec k
@[stacks 01JE "two-chart gluing"]
#check charts_cover k
#check standardCover k
#check glueData k
#check fromGlued k
#check gluedIso k
#check ι_fromGlued k
#check chartXIso k
#check chartYIso k
#check chartX_isAffineOpen k
#check chartY_isAffineOpen k
#check overlap_eq_chart_inf k
#check Overlap.sectionsIso k
@[stacks 01JE "inverse overlap coordinates"]
#check Overlap.xChartCoordinate_mul_yChartCoordinate k
#check XChart.toOverlap k
#check XChart.toOverlapAlgHom k
#check XChart.toOverlapAlgHom_toRingHom k
#check YChart.toOverlap k
#check YChart.toOverlapAlgHom k
#check YChart.toOverlapAlgHom_toRingHom k
#check restrictedCoordinates_mul k
@[stacks 01JE "global sections"]
#check ProjectiveSpace.globalSectionsComparison.isIso k 1
#check ProjectiveSpace.globalSectionsComparison k 1
@[stacks 01JE "nonaffineness"] #check not_isAffine k
@[stacks 01JE "infinitely many points"]
#check (inferInstance : Infinite (scheme k))
@[stacks 01JE "distinguished points"]
#check zeroPoint k
#check infinityPoint k
#check onePoint k
@[stacks 01JE "affine complement of one"]
#check awayOne_eq_compl_onePoint k
#check zeroPoint_mem_awayOne k
#check infinityPoint_mem_awayOne k
#check awayOne_isAffineOpen k
#check AwayOne.coordinate k
#check AwayOne.ringSectionsIso k
#check AwayOne.sectionsIso k
#check AwayOne.coordinateSection k
#check AwayOne.ringSectionsComparison_coordinate k
#check AwayOne.xPart k
#check AwayOne.yPart k
/- The indexed localization maps retain their natural algebra-hom structure over the
degree-zero homogeneous coordinate ring; the chart-specific ring maps are their views. -/
#check AwayOne.Part.fromAwayOneAlgHom k
#check AwayOne.Part.fromChartAlgHom k
#check AwayOne.XPart.sectionsIso k
#check AwayOne.XPart.fromAwayOneAlgHom k
#check AwayOne.XPart.fromXChartAlgHom k
#check AwayOne.XPart.fromAwayOneAlgHom_toRingHom k
#check AwayOne.XPart.fromXChartAlgHom_toRingHom k
#check AwayOne.XPart.coordinate_relation k
#check AwayOne.XPart.fromAwayOne_sectionsComparison k
#check AwayOne.YPart.sectionsIso k
#check AwayOne.YPart.fromAwayOneAlgHom k
#check AwayOne.YPart.fromYChartAlgHom k
#check AwayOne.YPart.fromAwayOneAlgHom_toRingHom k
#check AwayOne.YPart.fromYChartAlgHom_toRingHom k
#check AwayOne.YPart.coordinate_relation k
#check AwayOne.YPart.fromAwayOne_sectionsComparison k
#check XChart.restrictAwayOne k
#check YChart.restrictAwayOne k
#check AwayOne.coordinateSection_restrictX k
#check AwayOne.coordinateSection_restrictY k
@[stacks 01JE "affine-line identification"]
#check AwayOne.iso k

end AlgebraicGeometry.ProjectiveLine
