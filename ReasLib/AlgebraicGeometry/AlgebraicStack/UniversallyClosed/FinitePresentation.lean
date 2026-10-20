module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineSpace
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact

/-!
# Finite-presentation tests for universal closedness of algebraic stacks

Universal closedness of a quasi-compact morphism of algebraic stacks can be
tested on locally finitely presented affine base changes, or on all relative
affine spaces over a smooth surjective scheme atlas of the target.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Bicategory
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack

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
    (PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → Closed snd

/-- `forallAffineLocallyOfFinitePresentation f` means every affine
locally-of-finite-presentation 2-fibre-product projection of `f` is a closed
morphism. -/
theorem forallAffineLocallyOfFinitePresentation_iff :
    forallAffineLocallyOfFinitePresentation f ↔
      ∀ (Z : Over S) [IsAffine Z.left] (P : GroupoidsOver S) [AlgebraicStack P]
        (g : GroupoidsOver.slice Z ⟶ Y) [LocallyOfFinitePresentation g]
        (fst : P ⟶ X) (snd : P ⟶ GroupoidsOver.slice Z)
        (iso : fst ≫ f ≅ snd ≫ g),
        (PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → Closed snd := sorry

namespace forallAffineLocallyOfFinitePresentation

/-- A universal affine locally-of-finite-presentation 2-fibre-product condition
witnesses `forallAffineLocallyOfFinitePresentation f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : GroupoidsOver S}
    [AlgebraicStack P] {g : GroupoidsOver.slice Z ⟶ Y}
    [LocallyOfFinitePresentation g] {fst : P ⟶ X}
    {snd : P ⟶ GroupoidsOver.slice Z} (iso : fst ≫ f ≅ snd ≫ g),
    (PseudoPullbackCone.mk f g P fst snd iso).IsBilimit → Closed snd) :
    forallAffineLocallyOfFinitePresentation f := sorry

/-- Under `forallAffineLocallyOfFinitePresentation f`, the test-leg of any affine
locally-of-finite-presentation 2-fibre product of `f` is closed. -/
theorem spec (h : forallAffineLocallyOfFinitePresentation f) {Z : Over S}
    [IsAffine Z.left] {P : GroupoidsOver S} [AlgebraicStack P]
    {g : GroupoidsOver.slice Z ⟶ Y} [LocallyOfFinitePresentation g]
    {fst : P ⟶ X} {snd : P ⟶ GroupoidsOver.slice Z}
    (iso : fst ≫ f ≅ snd ≫ g) (hc : (PseudoPullbackCone.mk f g P fst snd iso).IsBilimit) :
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
        {fst : P ⟶ X} {snd : P ⟶ GroupoidsOver.slice (AlgebraicSpace.affineSpaceOver V n)}
        (iso : fst ≫ f ≅ snd ≫ (overMap (AlgebraicSpace.affineSpaceOver.proj V n) ≫ ψ)),
        (PseudoPullbackCone.mk f (overMap (AlgebraicSpace.affineSpaceOver.proj V n) ≫ ψ)
          P fst snd iso).IsBilimit → Closed snd

/-- `existsSmoothAffineSpace f` is the existence of a surjective smooth scheme
atlas of `Y` along which affine-space products of 2-fibre products of `f` are
closed. -/
theorem existsSmoothAffineSpace_iff : existsSmoothAffineSpace f ↔
    ∃ (V : Over S) (ψ : GroupoidsOver.slice V ⟶ Y),
      Groupoids.Hom.Smooth ψ ∧ Groupoids.Hom.Surjective ψ ∧
        ∀ (n : ℕ) (P : GroupoidsOver S) [AlgebraicStack P]
          (fst : P ⟶ X) (snd : P ⟶ GroupoidsOver.slice (AlgebraicSpace.affineSpaceOver V n))
          (iso : fst ≫ f ≅ snd ≫ (overMap (AlgebraicSpace.affineSpaceOver.proj V n) ≫ ψ)),
          (PseudoPullbackCone.mk f (overMap (AlgebraicSpace.affineSpaceOver.proj V n) ≫ ψ)
          P fst snd iso).IsBilimit → Closed snd := sorry

namespace existsSmoothAffineSpace

/-- A surjective smooth scheme atlas of `Y` with closed affine-space product
projections of 2-fibre products of `f` witnesses `existsSmoothAffineSpace f`. -/
theorem of {V : Over S} (ψ : GroupoidsOver.slice V ⟶ Y)
    [Groupoids.Hom.Smooth ψ] [Groupoids.Hom.Surjective ψ]
    (h : ∀ (n : ℕ) {P : GroupoidsOver S} [AlgebraicStack P]
      {fst : P ⟶ X} {snd : P ⟶ GroupoidsOver.slice (AlgebraicSpace.affineSpaceOver V n)}
      (iso : fst ≫ f ≅ snd ≫ (overMap (AlgebraicSpace.affineSpaceOver.proj V n) ≫ ψ)),
      (PseudoPullbackCone.mk f (overMap (AlgebraicSpace.affineSpaceOver.proj V n) ≫ ψ)
          P fst snd iso).IsBilimit → Closed snd) :
    existsSmoothAffineSpace f := sorry

/-- `existsSmoothAffineSpace f` supplies a surjective smooth scheme atlas of `Y`
along which affine-space products of 2-fibre products of `f` are closed. -/
theorem spec (h : existsSmoothAffineSpace f) :
    ∃ (V : Over S) (ψ : GroupoidsOver.slice V ⟶ Y),
      Groupoids.Hom.Smooth ψ ∧ Groupoids.Hom.Surjective ψ ∧
        ∀ (n : ℕ) {P : GroupoidsOver S} [AlgebraicStack P]
          {fst : P ⟶ X} {snd : P ⟶ GroupoidsOver.slice (AlgebraicSpace.affineSpaceOver V n)}
          (iso : fst ≫ f ≅ snd ≫ (overMap (AlgebraicSpace.affineSpaceOver.proj V n) ≫ ψ)),
          (PseudoPullbackCone.mk f (overMap (AlgebraicSpace.affineSpaceOver.proj V n) ≫ ψ)
          P fst snd iso).IsBilimit → Closed snd := sorry

end existsSmoothAffineSpace

end Closed

namespace UniversallyClosed

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiCompact f]

/-- For a quasi-compact morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks
over a scheme `S`, the following are equivalent: `UniversallyClosed f`; for
every morphism `Z ⟶ 𝒴` which is locally of finite presentation with `Z` an
affine scheme, the projection `|𝒳 ×_𝒴 Z| ⟶ |Z|` is closed; and there exists a
scheme `V` and a surjective smooth morphism `V ⟶ 𝒴` such that
`|𝔸(n) × (𝒳 ×_𝒴 V)| ⟶ |𝔸(n) × V|` is closed for every `n : ℕ`. -/
@[stacks 0H2A]
theorem tfae_quasiCompact :
    List.TFAE [UniversallyClosed f, Closed.forallAffineLocallyOfFinitePresentation f,
      Closed.existsSmoothAffineSpace f] := sorry

/-- A quasi-compact morphism of algebraic stacks is universally closed iff every
affine locally-of-finite-presentation base change has closed projection on
points. -/
theorem iff_forallAffineLocallyOfFinitePresentation :
    UniversallyClosed f ↔ Closed.forallAffineLocallyOfFinitePresentation f := sorry

/-- A quasi-compact morphism of algebraic stacks is universally closed iff some
surjective smooth scheme atlas of the target has closed affine-space product
projections. -/
theorem iff_existsSmoothAffineSpace :
    UniversallyClosed f ↔ Closed.existsSmoothAffineSpace f := sorry

end UniversallyClosed

end AlgebraicGeometry.AlgebraicStack
