/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Lemma_67_6_3_UniversallyOpen
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap74.Lemma_74_7_1_InverseImage
public import stacks_project.Chap78.Definition_78_18_1_Invariant
public import stacks_project.Chap78.Lemma_78_11_2_Groupoid

/-!
# Invariant saturation of open subspaces

Given a groupoid in algebraic spaces whose source and target maps are open, the
open `s(t⁻¹(W))` is the `R`-invariant saturation of an open subspace `W ⊂ U`.
When those maps are also quasi-compact, the object space admits a Zariski covering
by invariant quasi-compact open subspaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The underlying set of points of `s(t⁻¹(W))`, as the image of `t⁻¹(W)` under
`Points.map G.s.left`. -/
def sImageTPreimageSet (G : GroupoidAlgebraicSpace B) (W : OpenSubspace G.U.left) :
    Set (Points G.U.left) :=
  Points.map G.s.left '' (W.inverseImage G.t.left).pointsSet

/-- A point lies in `sImageTPreimageSet G W` iff it is the image under `G.s.left` of a
point of `t⁻¹(W)`. -/
theorem mem_sImageTPreimageSet (G : GroupoidAlgebraicSpace B)
    (W : OpenSubspace G.U.left) {x : Points G.U.left} :
    x ∈ sImageTPreimageSet G W ↔
      ∃ y, y ∈ (W.inverseImage G.t.left).pointsSet ∧ Points.map G.s.left y = x :=
  sorry

/-- If `s` and `t` are open, then the points-image `s(t⁻¹(W))` is open in the
canonical topology on `|U|`. -/
theorem isOpen_sImageTPreimageSet (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Open G.s.left] [AlgebraicSpace.Open G.t.left]
    (W : OpenSubspace G.U.left) :
    IsOpen (sImageTPreimageSet G W) := sorry

/-- The open subspace `s(t⁻¹(W)) ⊂ U` cut out by the points-image of `t⁻¹(W)`
along an open source map. -/
def sImageTPreimage (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Open G.s.left] [AlgebraicSpace.Open G.t.left]
    (W : OpenSubspace G.U.left) :
    OpenSubspace G.U.left :=
  OpenSubspace.ofOpens (Opens.mk (sImageTPreimageSet G W) (isOpen_sImageTPreimageSet G W))

/-- The points of `sImageTPreimage G W` are the image set `sImageTPreimageSet G W`. -/
theorem sImageTPreimage_pointsSet (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Open G.s.left] [AlgebraicSpace.Open G.t.left]
    (W : OpenSubspace G.U.left) :
    (sImageTPreimage G W).pointsSet = sImageTPreimageSet G W := sorry

/-- If `s` and `t` are open and quasi-compact, then the saturation of a
quasi-compact open subspace remains quasi-compact. -/
theorem isQuasiCompact_sImageTPreimage (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Open G.s.left] [AlgebraicSpace.Open G.t.left]
    [AlgebraicSpace.QuasiCompact G.s.left] [AlgebraicSpace.QuasiCompact G.t.left]
    (W : OpenSubspace G.U.left) [IsQuasiCompact W.X] :
    IsQuasiCompact (sImageTPreimage G W).X := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
