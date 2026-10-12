/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation

/-!
# Finite-presentation and étale affine-space tests for closed morphisms

A morphism of algebraic spaces may be tested for universal closedness, after a
quasi-compact hypothesis, by closedness of pullback projections along morphisms
locally of finite presentation, or by closedness of affine-space products after
passage to a surjective étale scheme atlas of the target.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

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

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The projection of every base change of `f` along a morphism locally of
finite presentation is a closed map on points. -/
def forallLocallyOfFinitePresentation : Prop :=
  ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y} [LocallyOfFinitePresentation g]
    {pZ : P ⟶ Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Closed pZ

/-- `forallLocallyOfFinitePresentation f` means every locally-of-finite-presentation
pullback projection of `f` is a closed morphism. -/
theorem forallLocallyOfFinitePresentation_iff :
    forallLocallyOfFinitePresentation f ↔
      ∀ (Z P : AlgebraicSpace S) (g : Z ⟶ Y) [LocallyOfFinitePresentation g]
        (pZ : P ⟶ Z) (pX : P ⟶ X),
        IsPullback pZ pX g f → Closed pZ := sorry

namespace forallLocallyOfFinitePresentation

/-- A universal locally-of-finite-presentation pullback condition witnesses
`forallLocallyOfFinitePresentation f`. -/
theorem of (h : ∀ {Z P : AlgebraicSpace S} {g : Z ⟶ Y}
    [LocallyOfFinitePresentation g] {pZ : P ⟶ Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Closed pZ) :
    forallLocallyOfFinitePresentation f := sorry

/-- Under `forallLocallyOfFinitePresentation f`, the test-leg of any
locally-of-finite-presentation pullback of `f` is closed. -/
theorem spec (h : forallLocallyOfFinitePresentation f) {Z P : AlgebraicSpace S}
    {g : Z ⟶ Y} [LocallyOfFinitePresentation g] {pZ : P ⟶ Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Closed pZ := sorry

/-- The chosen base-change projection `pullback.snd f g` is closed whenever
`g` is locally of finite presentation. -/
theorem pullback_snd (h : forallLocallyOfFinitePresentation f)
    {Z : AlgebraicSpace S} (g : Z ⟶ Y) [LocallyOfFinitePresentation g]
    [HasPullback f g] : Closed (pullback.snd f g) := sorry

end forallLocallyOfFinitePresentation

/-- There is a surjective étale morphism from a scheme to `Y` along which every
affine-space product of a pullback of `f` has closed projection on points. -/
def existsEtaleAffineSpace : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ (n : ℕ) {P : AlgebraicSpace S}
        {pA : P ⟶ ofOver (affineSpaceOver V n)} {pX : P ⟶ X},
        IsPullback pA pX (ofOverMap (affineSpaceOver.proj V n) ≫ ψ) f →
          Closed pA

/-- `existsEtaleAffineSpace f` is the existence of a surjective étale scheme atlas
of `Y` along which affine-space products of pullbacks of `f` are closed. -/
theorem existsEtaleAffineSpace_iff : existsEtaleAffineSpace f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (n : ℕ) (P : AlgebraicSpace S)
          (pA : P ⟶ ofOver (affineSpaceOver V n)) (pX : P ⟶ X),
          IsPullback pA pX (ofOverMap (affineSpaceOver.proj V n) ≫ ψ) f →
            Closed pA := sorry

namespace existsEtaleAffineSpace

/-- A surjective étale scheme atlas of `Y` with closed affine-space product
projections of pullbacks of `f` witnesses `existsEtaleAffineSpace f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ (n : ℕ) {P : AlgebraicSpace S}
      {pA : P ⟶ ofOver (affineSpaceOver V n)} {pX : P ⟶ X},
      IsPullback pA pX (ofOverMap (affineSpaceOver.proj V n) ≫ ψ) f →
        Closed pA) :
    existsEtaleAffineSpace f := sorry

/-- `existsEtaleAffineSpace f` supplies a surjective étale scheme atlas of `Y`
along which affine-space products of pullbacks of `f` are closed. -/
theorem spec (h : existsEtaleAffineSpace f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (n : ℕ) {P : AlgebraicSpace S}
          {pA : P ⟶ ofOver (affineSpaceOver V n)} {pX : P ⟶ X},
          IsPullback pA pX (ofOverMap (affineSpaceOver.proj V n) ≫ ψ) f →
            Closed pA := sorry

end existsEtaleAffineSpace

end Closed

end AlgebraicGeometry.AlgebraicSpace
