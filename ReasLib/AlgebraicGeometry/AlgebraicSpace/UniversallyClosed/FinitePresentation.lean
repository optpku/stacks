/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# Finite-presentation and étale affine-space tests for closed morphisms

A quasi-compact morphism of algebraic spaces is universally closed precisely when
its locally finitely presented base changes are closed, or when all affine-space
tests are closed after passage to a surjective étale scheme atlas of the target.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

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

namespace UniversallyClosed

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f]

/-- For a quasi-compact morphism `f : X ⟶ Y` of algebraic spaces
over a scheme `S`, the following are equivalent: `UniversallyClosed f`; every
base change of `f` along a morphism locally of finite presentation has closed
projection on points; and there exists a scheme `V` and a surjective étale
morphism `V ⟶ Y` such that each affine-space product of a pullback of `f` along
`𝔸(n; V) ⟶ Y` is closed on points for every `n : ℕ`. -/
theorem tfae_quasiCompact :
    List.TFAE [UniversallyClosed f, Closed.forallLocallyOfFinitePresentation f,
      Closed.existsEtaleAffineSpace f] := sorry

/-- A quasi-compact morphism of algebraic spaces is universally closed iff every
base change along a morphism locally of finite presentation has closed
projection on points. -/
theorem iff_forallLocallyOfFinitePresentation :
    UniversallyClosed f ↔ Closed.forallLocallyOfFinitePresentation f := sorry

/-- A quasi-compact morphism of algebraic spaces is universally closed iff some
surjective étale scheme atlas of the target has closed affine-space product
projections. -/
theorem iff_existsEtaleAffineSpace :
    UniversallyClosed f ↔ Closed.existsEtaleAffineSpace f := sorry

end UniversallyClosed

end AlgebraicGeometry.AlgebraicSpace
