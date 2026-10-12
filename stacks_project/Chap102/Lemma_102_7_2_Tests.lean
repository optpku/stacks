/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import stacks_project.Chap101.Definition_101_13_2_Closed
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Finite-presentation and smooth affine-space tests for closed morphisms of stacks

A quasi-compact morphism of algebraic stacks may be tested for universal
closedness by closedness of 2-fibre-product projections along morphisms from
affine schemes that are locally of finite presentation, or by closedness of
affine-space products after passage to a surjective smooth scheme atlas of the
target.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Affine `n`-space over a scheme `V` over `S`, viewed as an object of `Over S`. -/
def affineSpaceOver {S : Scheme.{u}} (V : Over S) (n : ℕ) : Over S :=
  Over.mk ((𝔸(ULift.{u} (Fin n); V.left) ↘ V.left) ≫ V.hom)

/-- The underlying scheme of `affineSpaceOver V n` is affine `n`-space over `V`. -/
theorem affineSpaceOver_left {S : Scheme.{u}} (V : Over S) (n : ℕ) :
    (affineSpaceOver V n).left = 𝔸(ULift.{u} (Fin n); V.left) := sorry

/-- The structure morphism of `affineSpaceOver V n` is the composite of the
relative affine-space projection with `V ⟶ S`. -/
theorem affineSpaceOver_hom {S : Scheme.{u}} (V : Over S) (n : ℕ) :
    (affineSpaceOver V n).hom =
      (𝔸(ULift.{u} (Fin n); V.left) ↘ V.left) ≫ V.hom := sorry

namespace affineSpaceOver

/-- The relative projection `𝔸(n; V) ⟶ V` in `Over S`. -/
def proj {S : Scheme.{u}} (V : Over S) (n : ℕ) : affineSpaceOver V n ⟶ V :=
  Over.homMk (𝔸(ULift.{u} (Fin n); V.left) ↘ V.left)

/-- The underlying scheme morphism of `proj V n` is the canonical affine-space
structure map over `V`. -/
theorem proj_left {S : Scheme.{u}} (V : Over S) (n : ℕ) :
    (proj V n).left = (𝔸(ULift.{u} (Fin n); V.left) ↘ V.left) := sorry

end affineSpaceOver

namespace Closed

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

/-- The projection of every base change of `f` along a locally-of-finite-presentation
morphism from an affine scheme is a closed map on points. -/
def forallAffineLocallyOfFinitePresentation : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : GroupoidsOver S} [AlgebraicStack P]
    {g : GroupoidsOver.slice Z ⟶ Y} [LocallyOfFinitePresentation g]
    {fst : P ⟶ X} {snd : P ⟶ GroupoidsOver.slice Z}
    (iso : fst ≫ f ≅ snd ≫ g),
    (Points.cone iso).IsBilimit → Closed snd

/-- `forallAffineLocallyOfFinitePresentation f` means every affine
locally-of-finite-presentation 2-fibre-product projection of `f` is a closed
morphism. -/
theorem forallAffineLocallyOfFinitePresentation_iff :
    forallAffineLocallyOfFinitePresentation f ↔
      ∀ (Z : Over S) [IsAffine Z.left] (P : GroupoidsOver S) [AlgebraicStack P]
        (g : GroupoidsOver.slice Z ⟶ Y) [LocallyOfFinitePresentation g]
        (fst : P ⟶ X) (snd : P ⟶ GroupoidsOver.slice Z)
        (iso : fst ≫ f ≅ snd ≫ g),
        (Points.cone iso).IsBilimit → Closed snd := sorry

namespace forallAffineLocallyOfFinitePresentation

/-- A universal affine locally-of-finite-presentation 2-fibre-product condition
witnesses `forallAffineLocallyOfFinitePresentation f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : GroupoidsOver S}
    [AlgebraicStack P] {g : GroupoidsOver.slice Z ⟶ Y}
    [LocallyOfFinitePresentation g] {fst : P ⟶ X}
    {snd : P ⟶ GroupoidsOver.slice Z} (iso : fst ≫ f ≅ snd ≫ g),
    (Points.cone iso).IsBilimit → Closed snd) :
    forallAffineLocallyOfFinitePresentation f := sorry

/-- Under `forallAffineLocallyOfFinitePresentation f`, the test-leg of any affine
locally-of-finite-presentation 2-fibre product of `f` is closed. -/
theorem spec (h : forallAffineLocallyOfFinitePresentation f) {Z : Over S}
    [IsAffine Z.left] {P : GroupoidsOver S} [AlgebraicStack P]
    {g : GroupoidsOver.slice Z ⟶ Y} [LocallyOfFinitePresentation g]
    {fst : P ⟶ X} {snd : P ⟶ GroupoidsOver.slice Z}
    (iso : fst ≫ f ≅ snd ≫ g) (hc : (Points.cone iso).IsBilimit) :
    Closed snd := sorry

end forallAffineLocallyOfFinitePresentation

/-- `forallAffineLocallyOfFinitePresentation f` is equivalent to closedness of
every chosen affine locally-of-finite-presentation projection `Z ×_Y X ⟶ Z`. -/
theorem forallAffineLocallyOfFinitePresentation_iff_twoFibreProduct_snd :
    forallAffineLocallyOfFinitePresentation f ↔
      ∀ {Z : Over S} [IsAffine Z.left] (g : GroupoidsOver.slice Z ⟶ Y)
        [LocallyOfFinitePresentation g]
        [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
        Closed (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) := sorry

/-- There is a surjective smooth morphism from a scheme to `Y` along which every
affine-space product of a 2-fibre product of `f` has closed projection on
points. -/
def existsSmoothAffineSpace : Prop :=
  ∃ (V : Over S) (ψ : GroupoidsOver.slice V ⟶ Y),
    Groupoids.Hom.Smooth ψ ∧ Groupoids.Hom.Surjective ψ ∧
      ∀ (n : ℕ) {P : GroupoidsOver S} [AlgebraicStack P]
        {fst : P ⟶ X} {snd : P ⟶ GroupoidsOver.slice (affineSpaceOver V n)}
        (iso : fst ≫ f ≅ snd ≫ (overMap (affineSpaceOver.proj V n) ≫ ψ)),
        (Points.cone iso).IsBilimit → Closed snd

/-- `existsSmoothAffineSpace f` is the existence of a surjective smooth scheme
atlas of `Y` along which affine-space products of 2-fibre products of `f` are
closed. -/
theorem existsSmoothAffineSpace_iff : existsSmoothAffineSpace f ↔
    ∃ (V : Over S) (ψ : GroupoidsOver.slice V ⟶ Y),
      Groupoids.Hom.Smooth ψ ∧ Groupoids.Hom.Surjective ψ ∧
        ∀ (n : ℕ) (P : GroupoidsOver S) [AlgebraicStack P]
          (fst : P ⟶ X) (snd : P ⟶ GroupoidsOver.slice (affineSpaceOver V n))
          (iso : fst ≫ f ≅ snd ≫ (overMap (affineSpaceOver.proj V n) ≫ ψ)),
          (Points.cone iso).IsBilimit → Closed snd := sorry

namespace existsSmoothAffineSpace

/-- A surjective smooth scheme atlas of `Y` with closed affine-space product
projections of 2-fibre products of `f` witnesses `existsSmoothAffineSpace f`. -/
theorem of {V : Over S} (ψ : GroupoidsOver.slice V ⟶ Y)
    [Groupoids.Hom.Smooth ψ] [Groupoids.Hom.Surjective ψ]
    (h : ∀ (n : ℕ) {P : GroupoidsOver S} [AlgebraicStack P]
      {fst : P ⟶ X} {snd : P ⟶ GroupoidsOver.slice (affineSpaceOver V n)}
      (iso : fst ≫ f ≅ snd ≫ (overMap (affineSpaceOver.proj V n) ≫ ψ)),
      (Points.cone iso).IsBilimit → Closed snd) :
    existsSmoothAffineSpace f := sorry

/-- `existsSmoothAffineSpace f` supplies a surjective smooth scheme atlas of `Y`
along which affine-space products of 2-fibre products of `f` are closed. -/
theorem spec (h : existsSmoothAffineSpace f) :
    ∃ (V : Over S) (ψ : GroupoidsOver.slice V ⟶ Y),
      Groupoids.Hom.Smooth ψ ∧ Groupoids.Hom.Surjective ψ ∧
        ∀ (n : ℕ) {P : GroupoidsOver S} [AlgebraicStack P]
          {fst : P ⟶ X} {snd : P ⟶ GroupoidsOver.slice (affineSpaceOver V n)}
          (iso : fst ≫ f ≅ snd ≫ (overMap (affineSpaceOver.proj V n) ≫ ψ)),
          (Points.cone iso).IsBilimit → Closed snd := sorry

end existsSmoothAffineSpace

end Closed

end AlgebraicGeometry.AlgebraicStack
