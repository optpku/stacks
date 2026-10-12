/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap101.Definition_101_13_2_Closed

/-!
# Local tests for universally closed morphisms of algebraic stacks

Universally closed morphisms of algebraic stacks may be tested by closed
projections after scheme-valued and affine base change, and by a surjective
smooth algebraic-space atlas of the target along which the base change is
universally closed.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace Closed

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

/-- The projection of every scheme-valued base change of `f` is a closed map on
points. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : GroupoidsOver S} [AlgebraicStack P]
    {g : GroupoidsOver.slice Z ⟶ Y} {fst : P ⟶ X}
    {snd : P ⟶ GroupoidsOver.slice Z} (iso : fst ≫ f ≅ snd ≫ g),
    (Points.cone iso).IsBilimit → Closed snd

/-- `forallScheme f` means every scheme-valued 2-fibre-product projection of `f`
is a closed morphism. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : GroupoidsOver S) [AlgebraicStack P]
      (g : GroupoidsOver.slice Z ⟶ Y) (fst : P ⟶ X)
      (snd : P ⟶ GroupoidsOver.slice Z) (iso : fst ≫ f ≅ snd ≫ g),
      (Points.cone iso).IsBilimit → Closed snd :=
  sorry

namespace forallScheme

/-- A universal scheme-valued 2-fibre-product condition witnesses
`forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : GroupoidsOver S} [AlgebraicStack P]
    {g : GroupoidsOver.slice Z ⟶ Y} {fst : P ⟶ X}
    {snd : P ⟶ GroupoidsOver.slice Z} (iso : fst ≫ f ≅ snd ≫ g),
    (Points.cone iso).IsBilimit → Closed snd) : forallScheme f :=
  sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued 2-fibre product of
`f` is closed. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : GroupoidsOver S}
    [AlgebraicStack P] {g : GroupoidsOver.slice Z ⟶ Y} {fst : P ⟶ X}
    {snd : P ⟶ GroupoidsOver.slice Z} (iso : fst ≫ f ≅ snd ≫ g)
    (hc : (Points.cone iso).IsBilimit) : Closed snd :=
  sorry

end forallScheme

/-- `forallScheme f` is equivalent to closedness of every chosen scheme-valued
projection `Z ×_Y X ⟶ Z`. -/
theorem forallScheme_iff_twoFibreProduct_snd : forallScheme f ↔
    ∀ {Z : Over S} (g : GroupoidsOver.slice Z ⟶ Y)
      [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
      Closed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- The projection of every affine-scheme-valued base change of `f` is a closed
map on points. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : GroupoidsOver S} [AlgebraicStack P]
    {g : GroupoidsOver.slice Z ⟶ Y} {fst : P ⟶ X}
    {snd : P ⟶ GroupoidsOver.slice Z} (iso : fst ≫ f ≅ snd ≫ g),
    (Points.cone iso).IsBilimit → Closed snd

/-- `forallAffine f` means every affine-scheme-valued 2-fibre-product projection
of `f` is a closed morphism. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : GroupoidsOver S) [AlgebraicStack P]
      (g : GroupoidsOver.slice Z ⟶ Y) (fst : P ⟶ X)
      (snd : P ⟶ GroupoidsOver.slice Z) (iso : fst ≫ f ≅ snd ≫ g),
      (Points.cone iso).IsBilimit → Closed snd :=
  sorry

namespace forallAffine

/-- A universal affine-scheme-valued 2-fibre-product condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : GroupoidsOver S}
    [AlgebraicStack P] {g : GroupoidsOver.slice Z ⟶ Y} {fst : P ⟶ X}
    {snd : P ⟶ GroupoidsOver.slice Z} (iso : fst ≫ f ≅ snd ≫ g),
    (Points.cone iso).IsBilimit → Closed snd) : forallAffine f :=
  sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued 2-fibre
product of `f` is closed. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : GroupoidsOver S} [AlgebraicStack P] {g : GroupoidsOver.slice Z ⟶ Y}
    {fst : P ⟶ X} {snd : P ⟶ GroupoidsOver.slice Z}
    (iso : fst ≫ f ≅ snd ≫ g) (hc : (Points.cone iso).IsBilimit) :
    Closed snd :=
  sorry

end forallAffine

/-- `forallAffine f` is equivalent to closedness of every chosen affine
scheme-valued projection `Z ×_Y X ⟶ Z`. -/
theorem forallAffine_iff_twoFibreProduct_snd : forallAffine f ↔
    ∀ {Z : Over S} [IsAffine Z.left] (g : GroupoidsOver.slice Z ⟶ Y)
      [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
      Closed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end Closed

namespace UniversallyClosed

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

/-- There is a surjective smooth morphism from an algebraic space to `Y` along
which every 2-fibre-product base change of `f` is universally closed. -/
def existsSmoothOnTarget : Prop :=
  ∃ (V : AlgebraicSpace S) (p : V.toGroupoids ⟶ Y),
    Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
      ∀ {P : GroupoidsOver S} [AlgebraicStack P] {fst : P ⟶ X}
        {snd : P ⟶ V.toGroupoids} (iso : fst ≫ f ≅ snd ≫ p),
        (Points.cone iso).IsBilimit → UniversallyClosed snd

/-- `existsSmoothOnTarget f` is the existence of a surjective smooth
algebraic-space atlas of `Y` along which 2-fibre-product base changes of `f`
are universally closed. -/
theorem existsSmoothOnTarget_iff : existsSmoothOnTarget f ↔
    ∃ (V : AlgebraicSpace S) (p : V.toGroupoids ⟶ Y),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        ∀ (P : GroupoidsOver S) [AlgebraicStack P] (fst : P ⟶ X)
          (snd : P ⟶ V.toGroupoids) (iso : fst ≫ f ≅ snd ≫ p),
          (Points.cone iso).IsBilimit → UniversallyClosed snd :=
  sorry

namespace existsSmoothOnTarget

/-- A surjective smooth algebraic-space atlas of `Y` with universally closed
2-fibre-product base changes of `f` witnesses `existsSmoothOnTarget f`. -/
theorem of {V : AlgebraicSpace S} (p : V.toGroupoids ⟶ Y)
    (hp_smooth : Groupoids.Hom.Smooth p) (hp_surj : Groupoids.Hom.Surjective p)
    (h : ∀ {P : GroupoidsOver S} [AlgebraicStack P] {fst : P ⟶ X}
      {snd : P ⟶ V.toGroupoids} (iso : fst ≫ f ≅ snd ≫ p),
      (Points.cone iso).IsBilimit → UniversallyClosed snd) :
    existsSmoothOnTarget f :=
  sorry

/-- `existsSmoothOnTarget f` supplies a surjective smooth algebraic-space atlas
of `Y` along which 2-fibre-product base changes of `f` are universally closed. -/
theorem spec (h : existsSmoothOnTarget f) :
    ∃ (V : AlgebraicSpace S) (p : V.toGroupoids ⟶ Y),
      Groupoids.Hom.Smooth p ∧ Groupoids.Hom.Surjective p ∧
        ∀ {P : GroupoidsOver S} [AlgebraicStack P] {fst : P ⟶ X}
          {snd : P ⟶ V.toGroupoids} (iso : fst ≫ f ≅ snd ≫ p),
          (Points.cone iso).IsBilimit → UniversallyClosed snd :=
  sorry

end existsSmoothOnTarget

end UniversallyClosed

end AlgebraicGeometry.AlgebraicStack
