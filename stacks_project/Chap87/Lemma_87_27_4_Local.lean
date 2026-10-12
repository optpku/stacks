/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap88.Definition_88_21_1_Formal
public import stacks_project.Chap88.Definition_88_20_1_Etale
public import stacks_project.Chap87.Lemma_87_27_3_ClosedImmersion

/-!
# Local tests for closed immersions of formal algebraic spaces

Closed immersions of functors of points may be tested on scheme-valued and
affine base change, on a Definition 87.11.1 étale atlas of the target, and on a
morphism of formal algebraic spaces that is representable by algebraic spaces,
surjective, flat, and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace ClosedImmersion

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)

/-- The projection of every scheme-valued base change of `f` is a closed
immersion. -/
def forallScheme : Prop :=
  ∀ {T : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
    {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X},
    IsPullback pT pX g f → ClosedImmersion pT

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is a
closed immersion. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (T : Over S) (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj T ⟶ Y)
      (pT : P ⟶ yoneda.obj T) (pX : P ⟶ X),
      IsPullback pT pX g f → ClosedImmersion pT := sorry

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {T : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
    {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X},
    IsPullback pT pX g f → ClosedImmersion pT) : forallScheme f := sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
a closed immersion. -/
theorem spec (h : forallScheme f) {T : Over S} {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj T ⟶ Y} {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X}
    (sq : IsPullback pT pX g f) : ClosedImmersion pT := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is a closed immersion whenever `forallScheme f` holds. -/
theorem pullback_snd {T : Over S} (h : forallScheme f) (g : yoneda.obj T ⟶ Y)
    [HasPullback f g] : ClosedImmersion (pullback.snd f g) := sorry

end forallScheme

/-- The projection of every affine-scheme-valued base change of `f` is a closed
immersion. -/
def forallAffine : Prop :=
  ∀ {T : Over S} [AlgebraicGeometry.IsAffine T.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj T ⟶ Y} {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X},
    IsPullback pT pX g f → ClosedImmersion pT

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is a closed immersion. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (T : Over S) [AlgebraicGeometry.IsAffine T.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj T ⟶ Y)
      (pT : P ⟶ yoneda.obj T) (pX : P ⟶ X),
      IsPullback pT pX g f → ClosedImmersion pT := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {T : Over S} [AlgebraicGeometry.IsAffine T.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
    {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X},
    IsPullback pT pX g f → ClosedImmersion pT) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is a closed immersion. -/
theorem spec (h : forallAffine f) {T : Over S}
    [AlgebraicGeometry.IsAffine T.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj T ⟶ Y} {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X}
    (sq : IsPullback pT pX g f) : ClosedImmersion pT := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is a closed immersion whenever `forallAffine f` holds. -/
theorem pullback_snd {T : Over S} [AlgebraicGeometry.IsAffine T.left]
    (h : forallAffine f) (g : yoneda.obj T ⟶ Y) [HasPullback f g] :
    ClosedImmersion (pullback.snd f g) := sorry

end forallAffine

/-- There is a Definition 87.11.1 covering of `Y` by affine formal algebraic
spaces, étale and jointly fppf-locally surjective, along which every pullback
of `f` is a closed immersion. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
    (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
      (∀ j, Etale (π j)) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) ∧
          (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
            IsPullback pY pX (π j) f → ClosedImmersion pY)

/-- `existsCoverOnTarget f` is the existence of a Definition 87.11.1 atlas of
`Y` along which pullbacks of `f` are closed immersions. -/
theorem existsCoverOnTarget_iff : existsCoverOnTarget f ↔
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (sigmaDesc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
              IsPullback pY pX (π j) f → ClosedImmersion pY) := sorry

namespace existsCoverOnTarget

/-- A Definition 87.11.1 atlas of `Y` with closed-immersion pullbacks of `f`
witnesses `existsCoverOnTarget f`. -/
theorem of {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : (j : ι) → Y_ j ⟶ Y)
    (hAffine : ∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j))
    (hEtale : ∀ j, Etale (π j))
    (hCover : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (sigmaDesc π))
    (hClosed : ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
      IsPullback pY pX (π j) f → ClosedImmersion pY) :
    existsCoverOnTarget f := sorry

/-- `existsCoverOnTarget f` supplies a Definition 87.11.1 atlas of `Y` along
which pullbacks of `f` are closed immersions. -/
theorem spec (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (sigmaDesc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
              IsPullback pY pX (π j) f → ClosedImmersion pY) := sorry

end existsCoverOnTarget

/-- There is a morphism of formal algebraic spaces to `Y`, representable by
algebraic spaces, surjective, flat, and locally of finite presentation, along
which every pullback of `f` is a closed immersion. -/
def existsFppf : Prop :=
  ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (_ : IsFormalAlgebraicSpace Z) (π : Z ⟶ Y)
    (hπ : AlgebraicSpace.representableByAlgebraicSpaces π),
    (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Surjective (hπ.pullbackHom ξ) ∧
        AlgebraicSpace.Flat (hπ.pullbackHom ξ) ∧
          AlgebraicSpace.LocallyOfFinitePresentation (hπ.pullbackHom ξ)) ∧
      ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX π f → ClosedImmersion pZ

/-- `existsFppf f` is the existence of a representable fppf morphism of formal
algebraic spaces to `Y` along which pullbacks of `f` are closed immersions. -/
theorem existsFppf_iff : existsFppf f ↔
    ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (_ : IsFormalAlgebraicSpace Z) (π : Z ⟶ Y)
      (hπ : AlgebraicSpace.representableByAlgebraicSpaces π),
      (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
        AlgebraicSpace.Surjective (hπ.pullbackHom ξ) ∧
          AlgebraicSpace.Flat (hπ.pullbackHom ξ) ∧
            AlgebraicSpace.LocallyOfFinitePresentation (hπ.pullbackHom ξ)) ∧
        ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X},
          IsPullback pZ pX π f → ClosedImmersion pZ := sorry

namespace existsFppf

/-- A representable fppf morphism of formal algebraic spaces to `Y` with
closed-immersion pullbacks of `f` witnesses `existsFppf f`. -/
theorem of {Z : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace Z] (π : Z ⟶ Y)
    (hπ : AlgebraicSpace.representableByAlgebraicSpaces π)
    (hFppf : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Surjective (hπ.pullbackHom ξ) ∧
        AlgebraicSpace.Flat (hπ.pullbackHom ξ) ∧
          AlgebraicSpace.LocallyOfFinitePresentation (hπ.pullbackHom ξ))
    (hClosed : ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X},
      IsPullback pZ pX π f → ClosedImmersion pZ) :
    existsFppf f := sorry

/-- `existsFppf f` supplies a morphism `π : Z ⟶ Y` of formal algebraic spaces
that is representable by algebraic spaces, surjective, flat, and locally of
finite presentation, together with closed immersions `X ×_Y Z ⟶ Z`. -/
theorem spec (h : existsFppf f) :
    ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (_ : IsFormalAlgebraicSpace Z) (π : Z ⟶ Y)
      (hπ : AlgebraicSpace.representableByAlgebraicSpaces π),
      (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
        AlgebraicSpace.Surjective (hπ.pullbackHom ξ) ∧
          AlgebraicSpace.Flat (hπ.pullbackHom ξ) ∧
            AlgebraicSpace.LocallyOfFinitePresentation (hπ.pullbackHom ξ)) ∧
        ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X},
          IsPullback pZ pX π f → ClosedImmersion pZ := sorry

end existsFppf

end ClosedImmersion

end AlgebraicGeometry.FormalAlgebraicSpace
