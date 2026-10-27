/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison

/-!
# Field-valued points versus points of algebraic spaces

The structural morphism induces a map from the points of an algebraic space to
its base scheme. Fixed-field points map to underlying points and to compatible
pairs of underlying points and field-valued points.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The component of `SchemeRealization.toBase X` at `T` is the unique morphism `T.unop ⟶ Over.mk (𝟙 S)`. -/
theorem toBase_app {S : Scheme.{u}} (X : AlgebraicSpace S) (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T) :
    (SchemeRealization.toBase X).app T x = Over.homMk T.unop.hom :=
  rfl

namespace Points

/-- The map `|X| → |S|` induced by the unique morphism from `X` to `S` as an
algebraic space over itself. -/
def base {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) : S :=
  (ofOver.pointsEquiv (Over.mk (𝟙 S))).symm (map (SchemeRealization.toBase X) x)

/-- The image of a field-valued point in `|S|` is the image of the unique point of
its source spectrum. -/
theorem base_mk {S : Scheme.{u}} {X : AlgebraicSpace S} (p : FieldValuedPoint X) :
    base (mk p) = p.structureHom default := by
  change p.structureHom (IsLocalRing.closedPoint p.K) = p.structureHom default
  exact congrArg p.structureHom (Subsingleton.elim _ _)

/-- The map `|X| → |S|` is invariant under morphisms of algebraic spaces over `S`. -/
theorem base_map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    base (map f x) = base x := by
  refine Quotient.inductionOn x ?_
  intro p
  rfl

end Points

/-- The point of `|X|` associated to a morphism `Spec K ⟶ X` over `S`. -/
def fieldPointsToPoints {S : Scheme.{u}} {X : AlgebraicSpace S} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) (p : ofOver (Over.mk σ) ⟶ X) : Points X :=
  Points.mk (FieldValuedPoint.of K σ p)

/-- `fieldPointsToPoints` is the class of the corresponding field-valued point. -/
theorem fieldPointsToPoints_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {K : Type u}
    [Field K] (σ : Spec (.of K) ⟶ S) (p : ofOver (Over.mk σ) ⟶ X) :
    fieldPointsToPoints σ p = Points.mk (FieldValuedPoint.of K σ p) :=
  rfl

/-- A `K`-point of `X` over `σ` lands in the fibre of `Points.base` over the image
of `σ`. -/
theorem fieldPointsToPoints_base {S : Scheme.{u}} {X : AlgebraicSpace S} {K : Type u}
    [Field K] (σ : Spec (.of K) ⟶ S) (p : ofOver (Over.mk σ) ⟶ X) :
    Points.base (fieldPointsToPoints σ p) = σ default :=
  Points.base_mk (FieldValuedPoint.of K σ p)

/-- The set-theoretic fibre product `|X| ×_{|Y|} Y(K)` of points with `K`-points of
`Y` over `S`. -/
abbrev pullbackFieldPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S) : Type (u + 1) :=
  Types.PullbackObj (TypeCat.ofHom (Points.map f))
    (TypeCat.ofHom fun p : ofOver (Over.mk σ) ⟶ Y ↦ fieldPointsToPoints σ p)

/-- A pair in `pullbackFieldPoints f σ` consists of a point of `X` and a `K`-point
of `Y` with the same image in `|Y|`. -/
theorem pullbackFieldPoints_condition {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S)
    (p : pullbackFieldPoints f σ) :
    Points.map f p.1.1 = fieldPointsToPoints σ p.1.2 :=
  p.2

/-- The comparison `X(K) → |X| ×_{|Y|} Y(K)` sending a `K`-point to its image in
`|X|` and its postcomposition in `Y(K)`. -/
def toPullbackFieldPoints {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S) (p : ofOver (Over.mk σ) ⟶ X) :
    pullbackFieldPoints f σ :=
  ⟨(fieldPointsToPoints σ p, p ≫ f), rfl⟩

/-- `toPullbackFieldPoints` is the compatible pair of the image in `|X|` and the
postcomposition in `Y(K)`. -/
theorem toPullbackFieldPoints_apply {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S)
    (p : ofOver (Over.mk σ) ⟶ X) :
    (toPullbackFieldPoints f σ p).1 = (fieldPointsToPoints σ p, p ≫ f) :=
  rfl

/-- The first component of `toPullbackFieldPoints f σ p` is the image of `p` in
`|X|`. -/
theorem toPullbackFieldPoints_fst {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S)
    (p : ofOver (Over.mk σ) ⟶ X) :
    (toPullbackFieldPoints f σ p).1.1 = fieldPointsToPoints σ p :=
  rfl

/-- The second component of `toPullbackFieldPoints f σ p` is the postcomposition
`p ≫ f`. -/
theorem toPullbackFieldPoints_snd {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S)
    (p : ofOver (Over.mk σ) ⟶ X) :
    (toPullbackFieldPoints f σ p).1.2 = p ≫ f :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
