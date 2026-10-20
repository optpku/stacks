/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.CategoryTheory.Subobject.Invariant

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
  OpenSubspace.fromOpens
    (Opens.mk (sImageTPreimageSet G W) (isOpen_sImageTPreimageSet G W))

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

/-- For a groupoid in algebraic spaces with open source and target maps, the
saturation `s(t⁻¹(W))` of every open subspace `W` is invariant. -/
@[stacks 044G]
theorem isOpenInvariant_sImageTPreimage {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Open G.s.left] [AlgebraicSpace.Open G.t.left]
    (W : OpenSubspace G.U.left) :
    CategoryTheory.Morphism.IsForwardInvariant G.s.left G.t.left
      (sImageTPreimage G W).ι := sorry

/-- A groupoid in algebraic spaces with open quasi-compact source and target maps
admits a small Zariski covering of its object space by invariant quasi-compact
open subspaces. -/
@[stacks 044G]
theorem exists_invariantQuasiCompactOpenCover {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Open G.s.left] [AlgebraicSpace.Open G.t.left]
    [AlgebraicSpace.QuasiCompact G.s.left] [AlgebraicSpace.QuasiCompact G.t.left] :
    ∃ (ι : Type u) (_ : Small.{u} ι) (𝒰 : ι → OpenSubspace G.U.left),
      IsZariskiCover G.U.left (fun i ↦ (𝒰 i).X) (fun i ↦ (𝒰 i).ι) ∧
        ∀ i, CategoryTheory.Morphism.IsForwardInvariant G.s.left G.t.left (𝒰 i).ι ∧
          IsQuasiCompact (𝒰 i).X := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
