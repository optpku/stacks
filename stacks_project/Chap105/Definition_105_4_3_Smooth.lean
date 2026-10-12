/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Smooth morphisms from schemes to categories fibred in groupoids

A 1-morphism `slice S ⟶ X` is smooth on schemes when it is relatively
representable and every scheme representing a 2-fibre product with a test
morphism `slice S' ⟶ X` has smooth projection to `S'`.
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

/-- A 1-morphism from a scheme slice to a category fibred in groupoids over
`Over B` (for example `S ⟶ ℳ_{1,1}`) is smooth when it is relatively
representable and, for every test morphism `S' ⟶ X`, every scheme representing
the 2-fibre product has smooth projection `S ×_X S' ⟶ S'`. -/
class SmoothOnSchemes {B : Scheme.{u}} {X : GroupoidsOver B} {S : Over B}
    (f : GroupoidsOver.slice S ⟶ X) : Prop where
  /-- The 1-morphism is relatively representable. -/
  representable : FiberedCategoryOver.Groupoids.relativelyRepresentable f
  /-- Every representing projection of a scheme-theoretic fibre product is a
  smooth morphism of schemes. -/
  of_represents : ∀ ⦃S' : Over B⦄ (g : GroupoidsOver.slice S' ⟶ X)
    (W : Over B) (π : W ⟶ S'),
    RepresentsSchemeBaseChange f g W π → AlgebraicGeometry.Smooth π.left

namespace SmoothOnSchemes

/-- The identity 1-morphism of a scheme slice is smooth on schemes. -/
instance id {B : Scheme.{u}} {S : Over B} :
    SmoothOnSchemes (𝟙 (GroupoidsOver.slice S)) := sorry

/-- The 1-morphism of slice fibrations induced by a smooth morphism of schemes
is smooth on schemes. -/
instance ofSmooth {B : Scheme.{u}} {S T : Over B} (h : S ⟶ T)
    [AlgebraicGeometry.Smooth h.left] :
    SmoothOnSchemes (overMap h) := sorry

/-- A representing projection for a 1-morphism that is smooth on schemes is a
smooth morphism of schemes. -/
theorem spec {B : Scheme.{u}} {X : GroupoidsOver B} {S : Over B}
    (f : GroupoidsOver.slice S ⟶ X) [SmoothOnSchemes f] {S' : Over B}
    (g : GroupoidsOver.slice S' ⟶ X) {W : Over B} {π : W ⟶ S'}
    (h : RepresentsSchemeBaseChange f g W π) :
    AlgebraicGeometry.Smooth π.left := sorry

/-- A 1-morphism that is smooth on schemes is relatively representable. -/
theorem relativelyRepresentable {B : Scheme.{u}} {X : GroupoidsOver B}
    {S : Over B} (f : GroupoidsOver.slice S ⟶ X) [SmoothOnSchemes f] :
    FiberedCategoryOver.Groupoids.relativelyRepresentable f := sorry

/-- A relatively representable 1-morphism from a scheme slice whose representing
projections are smooth is smooth on schemes. -/
theorem of {B : Scheme.{u}} {X : GroupoidsOver B} {S : Over B}
    {f : GroupoidsOver.slice S ⟶ X}
    (hrep : FiberedCategoryOver.Groupoids.relativelyRepresentable f)
    (hsm : ∀ ⦃S' : Over B⦄ (g : GroupoidsOver.slice S' ⟶ X) (W : Over B)
      (π : W ⟶ S'),
      RepresentsSchemeBaseChange f g W π → AlgebraicGeometry.Smooth π.left) :
    SmoothOnSchemes f := sorry

/-- A 1-morphism from a scheme slice is smooth on schemes if and only if it is
relatively representable and every representing projection is a smooth morphism
of schemes. -/
theorem iff {B : Scheme.{u}} {X : GroupoidsOver B} {S : Over B}
    (f : GroupoidsOver.slice S ⟶ X) :
    SmoothOnSchemes f ↔
      FiberedCategoryOver.Groupoids.relativelyRepresentable f ∧
        ∀ ⦃S' : Over B⦄ (g : GroupoidsOver.slice S' ⟶ X) (W : Over B)
          (π : W ⟶ S'),
          RepresentsSchemeBaseChange f g W π →
            AlgebraicGeometry.Smooth π.left := sorry

end SmoothOnSchemes

end AlgebraicGeometry.Groupoids.Hom
