module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.SliceBaseChange
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map

/-!
# Scheme representations of slice base changes

A scheme represents a slice base change when its slice fibration is equivalent
to the two-fibre-product apex and the equivalence respects the projection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A slice 2-fibre product of `f` along `y : GroupoidsOver.slice U ⟶ Y` is
represented by a scheme `W` over `B` with structure morphism `π : W ⟶ U` when
the apex is equivalent to `GroupoidsOver.slice W` and the projection triangle
identifies `overMap π` with `TwoFibreProduct.fst`. -/
def RepresentsSchemeBaseChange {B : Scheme.{u}} {X Y : GroupoidsOver B}
    (f : X ⟶ Y) {U : Over B} (y : GroupoidsOver.slice U ⟶ Y) (W : Over B)
    (π : W ⟶ U) : Prop :=
  ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌ GroupoidsOver.slice W,
    Nonempty
      (e.hom ≫ overMap π ≅ TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f)

/-- A representing scheme is equivalent to the slice 2-fibre product. -/
theorem RepresentsSchemeBaseChange.apex_equivalence {B : Scheme.{u}}
    {X Y : GroupoidsOver B} {f : X ⟶ Y} {U : Over B}
    {y : GroupoidsOver.slice U ⟶ Y} {W : Over B} {π : W ⟶ U}
    (h : RepresentsSchemeBaseChange f y W π) :
    Nonempty (TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌
      GroupoidsOver.slice W) := sorry

/-- The structure morphism of a representing scheme recovers the projection of
the slice 2-fibre product. -/
theorem RepresentsSchemeBaseChange.projection_triangle {B : Scheme.{u}}
    {X Y : GroupoidsOver B} {f : X ⟶ Y} {U : Over B}
    {y : GroupoidsOver.slice U ⟶ Y} {W : Over B} {π : W ⟶ U}
    (h : RepresentsSchemeBaseChange f y W π) :
    ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌ GroupoidsOver.slice W,
      Nonempty
        (e.hom ≫ overMap π ≅ TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f) :=
  sorry

/-- Representing a slice 2-fibre product by a scheme means the apex is
equivalent to that scheme's slice, with `overMap π` identified to
`TwoFibreProduct.fst`. -/
theorem RepresentsSchemeBaseChange.iff {B : Scheme.{u}} {X Y : GroupoidsOver B}
    {f : X ⟶ Y} {U : Over B} {y : GroupoidsOver.slice U ⟶ Y} {W : Over B}
    {π : W ⟶ U} :
    RepresentsSchemeBaseChange f y W π ↔
      ∃ e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} y f ≌ GroupoidsOver.slice W,
        Nonempty
          (e.hom ≫ overMap π ≅ TwoFibreProduct.fst.{u + 1, u, u + 1, u} y f) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
