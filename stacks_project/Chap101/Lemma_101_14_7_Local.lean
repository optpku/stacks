/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import stacks_project.Chap101.Definition_101_14_2_UniversallyInjective

/-!
# Affine tests for universally injective morphisms of algebraic stacks

Universally injective morphisms of algebraic stacks may be tested by
universally injective projections after affine-scheme-valued base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversallyInjective

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

/-- The projection of every affine-scheme-valued base change of `f` is
universally injective. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : GroupoidsOver S} [AlgebraicStack P]
    {g : GroupoidsOver.slice Z ⟶ Y} {fst : P ⟶ X}
    {snd : P ⟶ GroupoidsOver.slice Z} (iso : fst ≫ f ≅ snd ≫ g),
    (Points.cone iso).IsBilimit → UniversallyInjective snd

/-- `forallAffine f` means every affine-scheme-valued 2-fibre-product projection
of `f` is universally injective. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : GroupoidsOver S) [AlgebraicStack P]
      (g : GroupoidsOver.slice Z ⟶ Y) (fst : P ⟶ X)
      (snd : P ⟶ GroupoidsOver.slice Z) (iso : fst ≫ f ≅ snd ≫ g),
      (Points.cone iso).IsBilimit → UniversallyInjective snd :=
  sorry

namespace forallAffine

/-- A universal affine-scheme-valued 2-fibre-product condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : GroupoidsOver S}
    [AlgebraicStack P] {g : GroupoidsOver.slice Z ⟶ Y} {fst : P ⟶ X}
    {snd : P ⟶ GroupoidsOver.slice Z} (iso : fst ≫ f ≅ snd ≫ g),
    (Points.cone iso).IsBilimit → UniversallyInjective snd) : forallAffine f :=
  sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued 2-fibre
product of `f` is universally injective. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : GroupoidsOver S} [AlgebraicStack P] {g : GroupoidsOver.slice Z ⟶ Y}
    {fst : P ⟶ X} {snd : P ⟶ GroupoidsOver.slice Z}
    (iso : fst ≫ f ≅ snd ≫ g) (hc : (Points.cone iso).IsBilimit) :
    UniversallyInjective snd :=
  sorry

end forallAffine

/-- `forallAffine f` is equivalent to universal injectivity of every chosen
affine scheme-valued projection `Z ×_Y X ⟶ Z`. -/
theorem forallAffine_iff_twoFibreProduct_snd : forallAffine f ↔
    ∀ {Z : Over S} [IsAffine Z.left] (g : GroupoidsOver.slice Z ⟶ Y)
      [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
      UniversallyInjective (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end UniversallyInjective

end AlgebraicGeometry.AlgebraicStack
