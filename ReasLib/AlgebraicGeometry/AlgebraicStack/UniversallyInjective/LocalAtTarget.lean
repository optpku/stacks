module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct

/-!
# Affine tests for universally injective morphisms of algebraic stacks

A morphism of algebraic stacks is universally injective if and only if every
affine-scheme-valued base change has universally injective projection.
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
    (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit →
      UniversallyInjective snd

/-- `forallAffine f` means every affine-scheme-valued 2-fibre-product projection
of `f` is universally injective. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : GroupoidsOver S) [AlgebraicStack P]
      (g : GroupoidsOver.slice Z ⟶ Y) (fst : P ⟶ X)
      (snd : P ⟶ GroupoidsOver.slice Z) (iso : fst ≫ f ≅ snd ≫ g),
      (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit →
        UniversallyInjective snd :=
  sorry

namespace forallAffine

/-- A universal affine-scheme-valued 2-fibre-product condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : GroupoidsOver S}
    [AlgebraicStack P] {g : GroupoidsOver.slice Z ⟶ Y} {fst : P ⟶ X}
    {snd : P ⟶ GroupoidsOver.slice Z} (iso : fst ≫ f ≅ snd ≫ g),
    (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit →
      UniversallyInjective snd) : forallAffine f :=
  sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued 2-fibre
product of `f` is universally injective. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : GroupoidsOver S} [AlgebraicStack P] {g : GroupoidsOver.slice Z ⟶ Y}
    {fst : P ⟶ X} {snd : P ⟶ GroupoidsOver.slice Z}
    (iso : fst ≫ f ≅ snd ≫ g)
    (hc : (CategoryTheory.Bicategory.PseudoPullbackCone.mk f g P fst snd iso).IsBilimit) :
    UniversallyInjective snd :=
  sorry

end forallAffine

/-- `forallAffine f` is equivalent to universal injectivity of every chosen
affine scheme-valued projection `Z ×_Y X ⟶ Z`. -/
theorem forallAffine_iff_twoFibreProduct_snd : forallAffine f ↔
    ∀ {Z : Over S} [IsAffine Z.left] (g : GroupoidsOver.slice Z ⟶ Y),
      UniversallyInjective (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

/-- A morphism of algebraic stacks is universally injective if and only if every
affine-scheme-valued base change is universally injective. -/
@[stacks 0DTN]
theorem iff_forallAffine : UniversallyInjective f ↔ forallAffine f :=
  sorry

end UniversallyInjective

end AlgebraicGeometry.AlgebraicStack
