module

public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable

/-!
# Completion of an algebraic space along a closed subset

The completion `completionAlong X T` of an algebraic space `X` along a closed
subset `T ⊆ Points X` is the subfunctor of `X.functorOfPoints` classifying
morphisms from schemes over `S` whose image of points lands in `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A Yoneda section of `X` maps into `T` when the induced map on underlying points
of the source scheme lands in `T`. -/
def mapsInto {S : Scheme.{u}} {X : AlgebraicSpace S} (T : Set (Points X))
    {U : Over S} (x : X.functorOfPoints.obj (op U)) : Prop :=
  Set.range (Points.mapOfOver (yonedaEquiv.symm x : ofOver U ⟶ X)) ⊆ T

/-- `mapsInto T x` means that the image of `|U|` under the morphism classified by `x`
is contained in `T`. -/
theorem mapsInto_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (T : Set (Points X))
    {U : Over S} (x : X.functorOfPoints.obj (op U)) :
    mapsInto T x ↔
      Set.range (Points.mapOfOver (yonedaEquiv.symm x : ofOver U ⟶ X)) ⊆ T :=
  sorry

/-- `mapsInto` is stable under precomposition with a morphism of schemes over `S`. -/
theorem mapsInto_map {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Set (Points X)}
    {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) {x : X.functorOfPoints.obj U}
    (hx : mapsInto T x) : mapsInto T (X.functorOfPoints.map φ x) :=
  sorry

/-- If a section of `X'` maps into the closed preimage of `T` along `f : X' ⟶ X`, then
the postcomposition with `f` maps into `T`. -/
theorem mapsInto_comp {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) {U : Over S} {x : X'.functorOfPoints.obj (op U)}
    (hx : mapsInto (T.preimage (Points.continuous_map f) : Set (Points X')) x) :
    mapsInto (T : Set (Points X)) (f.app (op U) x) :=
  sorry

/-- The completion of an algebraic space `X` along a closed subset `T ⊆ Points X`,
as the subfunctor of `X.functorOfPoints` classifying morphisms from schemes whose
image of points lands in `T`. -/
def completionAlong {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj U := { x : X.functorOfPoints.obj U // mapsInto (T : Set (Points X)) x }
  map φ := ofHom fun x ↦ ⟨X.functorOfPoints.map φ x.1, mapsInto_map φ x.2⟩
  map_id := by
    intro U
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    change X.functorOfPoints.map (𝟙 U) x.1 = x.1
    rw [X.functorOfPoints.map_id]
    rfl
  map_comp := by
    intro U V W φ ψ
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    change X.functorOfPoints.map (φ ≫ ψ) x.1 =
      X.functorOfPoints.map ψ (X.functorOfPoints.map φ x.1)
    rw [X.functorOfPoints.map_comp]
    rfl

namespace completionAlong

/-- The canonical morphism `completionAlong X T ⟶ X.functorOfPoints` from the
completion along `T`. -/
def ι {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    completionAlong X T ⟶ X.functorOfPoints where
  app _ := ofHom fun x ↦ x.1
  naturality := by intros; rfl

/-- Components of `ι X T` are the subtype projections of `completionAlong X T`. -/
theorem ι_app {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Closeds (Points X))
    (U : (Over S)ᵒᵖ) : (ι X T).app U = ofHom fun x ↦ x.1 :=
  sorry

/-- A Yoneda section of `X` maps into `T` if and only if it lifts through
`ι X T`. -/
theorem exists_lift {S : Scheme.{u}} {X : AlgebraicSpace S} (T : Closeds (Points X))
    {U : Over S} (x : X.functorOfPoints.obj (op U)) :
    mapsInto (T : Set (Points X)) x ↔ ∃ y, (ι X T).app (op U) y = x :=
  sorry

/-- A morphism `f : X' ⟶ X` induces a map from the completion of `X'` along the
preimage of `T` into the completion of `X` along `T`. -/
def map {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) :
    completionAlong X' (T.preimage (Points.continuous_map f)) ⟶
      completionAlong X T where
  app U := ofHom fun x ↦ ⟨f.app U x.1, mapsInto_comp f T x.2⟩
  naturality := by
    intro U V φ
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact congrArg (fun k : X'.functorOfPoints.obj U ⟶ X.functorOfPoints.obj V ↦ k x.1)
      (f.naturality φ)

/-- The underlying section of `map f T` is the component of `f`. -/
theorem map_app {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) (U : (Over S)ᵒᵖ)
    (x : (completionAlong X' (T.preimage (Points.continuous_map f))).obj U) :
    (ι X T).app U ((map f T).app U x) =
      f.app U ((ι X' (T.preimage (Points.continuous_map f))).app U x) :=
  sorry

end completionAlong

/-- For a morphism `f : X' ⟶ X` of algebraic spaces over a scheme
`S` and a closed subset `T ⊆ Points X`, writing `T'` for
`T.preimage (Points.continuous_map f)`, the square
`completionAlong X' T' ⟶ X'.functorOfPoints` over
`completionAlong X T ⟶ X.functorOfPoints` is cartesian in
`(Over S)ᵒᵖ ⥤ Type u`. -/
theorem completionAlong_isPullback {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) :
    IsPullback (completionAlong.ι X' (T.preimage (Points.continuous_map f)))
      (completionAlong.map f T) f (completionAlong.ι X T) :=
  sorry

/-- The map from the completion along the preimage of a closed subset to the
completion along that subset is representable by algebraic spaces. -/
theorem representableByAlgebraicSpaces_completionAlong_map
    {S : Scheme.{u}} {X' X : AlgebraicSpace S} (f : X' ⟶ X)
    (T : Closeds (Points X)) :
    representableByAlgebraicSpaces (completionAlong.map f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
