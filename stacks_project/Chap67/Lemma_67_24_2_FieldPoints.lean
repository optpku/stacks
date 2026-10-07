module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison

/-!
# Field-valued points versus points of algebraic spaces

The unique morphism from an algebraic space `X` over `S` to `S` as an algebraic
space induces `|X| → |S|`. Field-valued points over a morphism `Spec K ⟶ S` map
to `|X|` and to the fibre product `|X| ×_{|Y|} Y(K)`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The unique morphism from an algebraic space over `S` to `S` viewed as an
algebraic space over itself. -/
def toBase {S : Scheme.{u}} (X : AlgebraicSpace S) : X ⟶ ofOver (Over.mk (𝟙 S)) where
  app T := ↾fun _ ↦ Over.homMk T.unop.hom
  naturality := sorry

/-- The component of `toBase X` at `T` is the unique morphism `T.unop ⟶ Over.mk (𝟙 S)`. -/
theorem toBase_app {S : Scheme.{u}} (X : AlgebraicSpace S) (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T) :
    (toBase X).app T x = Over.homMk T.unop.hom :=
  sorry

/-- Any morphism from `X` to `S` as an algebraic space over itself equals `toBase X`. -/
theorem eq_toBase {S : Scheme.{u}} {X : AlgebraicSpace S}
    (f : X ⟶ ofOver (Over.mk (𝟙 S))) : f = toBase X :=
  sorry

namespace Points

/-- The map `|X| → |S|` induced by the unique morphism from `X` to `S` as an
algebraic space over itself. -/
def base {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) : S :=
  (ofOver.pointsEquiv (Over.mk (𝟙 S))).symm (map (toBase X) x)

/-- The image of a field-valued point in `|S|` is the image of the unique point of
its source spectrum. -/
theorem base_mk {S : Scheme.{u}} {X : AlgebraicSpace S} (p : FieldValuedPoint X) :
    base (mk p) = p.structureHom default :=
  sorry

/-- The map `|X| → |S|` is invariant under morphisms of algebraic spaces over `S`. -/
theorem base_map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    base (map f x) = base x :=
  sorry

end Points

/-- The point of `|X|` associated to a morphism `Spec K ⟶ X` over `S`. -/
def fieldPointsToPoints {S : Scheme.{u}} {X : AlgebraicSpace S} {K : Type u} [Field K]
    (σ : Spec (.of K) ⟶ S) (p : ofOver (Over.mk σ) ⟶ X) : Points X :=
  Points.mk (FieldValuedPoint.of K σ p)

/-- `fieldPointsToPoints` is the class of the corresponding field-valued point. -/
theorem fieldPointsToPoints_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {K : Type u}
    [Field K] (σ : Spec (.of K) ⟶ S) (p : ofOver (Over.mk σ) ⟶ X) :
    fieldPointsToPoints σ p = Points.mk (FieldValuedPoint.of K σ p) :=
  sorry

/-- A `K`-point of `X` over `σ` lands in the fibre of `Points.base` over the image
of `σ`. -/
theorem fieldPointsToPoints_base {S : Scheme.{u}} {X : AlgebraicSpace S} {K : Type u}
    [Field K] (σ : Spec (.of K) ⟶ S) (p : ofOver (Over.mk σ) ⟶ X) :
    Points.base (fieldPointsToPoints σ p) = σ default :=
  sorry

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
  sorry

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
  sorry

/-- The first component of `toPullbackFieldPoints f σ p` is the image of `p` in
`|X|`. -/
theorem toPullbackFieldPoints_fst {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S)
    (p : ofOver (Over.mk σ) ⟶ X) :
    (toPullbackFieldPoints f σ p).1.1 = fieldPointsToPoints σ p :=
  sorry

/-- The second component of `toPullbackFieldPoints f σ p` is the postcomposition
`p ≫ f`. -/
theorem toPullbackFieldPoints_snd {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {K : Type u} [Field K] (σ : Spec (.of K) ⟶ S)
    (p : ofOver (Over.mk σ) ⟶ X) :
    (toPullbackFieldPoints f σ p).1.2 = p ≫ f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
