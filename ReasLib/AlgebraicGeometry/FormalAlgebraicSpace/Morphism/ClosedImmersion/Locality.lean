/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation

/-!
# Local criteria for closed immersions of formal algebraic spaces

The closed-immersion property of a morphism of formal algebraic spaces can be
tested after scheme and affine base change, on an etale atlas, or after a
representable fppf base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace ClosedImmersion

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)

/-- Every scheme-valued base change of `f` has closed-immersion projection. -/
def forallScheme : Prop :=
  ∀ {T : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
    {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X},
    IsPullback pT pX g f → ClosedImmersion pT

/-- The quantified form of `forallScheme f`. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (T : Over S) (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj T ⟶ Y)
      (pT : P ⟶ yoneda.obj T) (pX : P ⟶ X),
      IsPullback pT pX g f → ClosedImmersion pT := sorry

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {T : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
    {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X},
    IsPullback pT pX g f → ClosedImmersion pT) : forallScheme f := sorry

/-- Under `forallScheme f`, every scheme-valued pullback projection is closed. -/
theorem spec (h : forallScheme f) {T : Over S} {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj T ⟶ Y} {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X}
    (sq : IsPullback pT pX g f) : ClosedImmersion pT := sorry

/-- The selected pullback projection from a scheme is closed under `forallScheme`. -/
theorem pullback_snd {T : Over S} (h : forallScheme f) (g : yoneda.obj T ⟶ Y)
    [HasPullback f g] : ClosedImmersion (pullback.snd f g) := sorry

end forallScheme

/-- Every affine-scheme-valued base change of `f` has closed-immersion projection. -/
def forallAffine : Prop :=
  ∀ {T : Over S} [AlgebraicGeometry.IsAffine T.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj T ⟶ Y} {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X},
    IsPullback pT pX g f → ClosedImmersion pT

/-- The quantified form of `forallAffine f`. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (T : Over S) [AlgebraicGeometry.IsAffine T.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj T ⟶ Y)
      (pT : P ⟶ yoneda.obj T) (pX : P ⟶ X),
      IsPullback pT pX g f → ClosedImmersion pT := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses `forallAffine f`. -/
theorem of (h : ∀ {T : Over S} [AlgebraicGeometry.IsAffine T.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
    {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X},
    IsPullback pT pX g f → ClosedImmersion pT) : forallAffine f := sorry

/-- Under `forallAffine f`, every tested projection is a closed immersion. -/
theorem spec (h : forallAffine f) {T : Over S}
    [AlgebraicGeometry.IsAffine T.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj T ⟶ Y} {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X}
    (sq : IsPullback pT pX g f) : ClosedImmersion pT := sorry

/-- The selected pullback projection from an affine scheme is closed under `forallAffine`. -/
theorem pullback_snd {T : Over S} [AlgebraicGeometry.IsAffine T.left]
    (h : forallAffine f) (g : yoneda.obj T ⟶ Y) [HasPullback f g] :
    ClosedImmersion (pullback.snd f g) := sorry

end forallAffine

/-- An etale covering of `Y` by formal algebraic spaces, each obtained as a
directed colimit of affine thickenings and jointly fppf-surjective over `Y`,
has closed pullbacks of `f`. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
    (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
      (∀ j, Etale (π j)) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) ∧
          (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
            IsPullback pY pX (π j) f → ClosedImmersion pY)

/-- The explicit quantified form of `existsCoverOnTarget f`. -/
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

/-- An etale covering with closed pullbacks witnesses `existsCoverOnTarget f`. -/
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

/-- `existsCoverOnTarget f` supplies the covering family and its closed pullbacks. -/
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

/-- A representable, surjective, flat, locally finitely presented base change of `Y`
has closed-immersion pullback projection. -/
def existsFppf : Prop :=
  ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (_ : IsFormalAlgebraicSpace Z) (π : Z ⟶ Y)
    (hπ : AlgebraicSpace.representableByAlgebraicSpaces π),
    (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Surjective (hπ.pullbackHom ξ) ∧
        AlgebraicSpace.Flat (hπ.pullbackHom ξ) ∧
          AlgebraicSpace.LocallyOfFinitePresentation (hπ.pullbackHom ξ)) ∧
      ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX π f → ClosedImmersion pZ

/-- The explicit quantified form of `existsFppf f`. -/
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

/-- A representable fppf base change with closed pullbacks witnesses `existsFppf f`. -/
theorem of {Z : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace Z] (π : Z ⟶ Y)
    (hπ : AlgebraicSpace.representableByAlgebraicSpaces π)
    (hFppf : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Surjective (hπ.pullbackHom ξ) ∧
        AlgebraicSpace.Flat (hπ.pullbackHom ξ) ∧
          AlgebraicSpace.LocallyOfFinitePresentation (hπ.pullbackHom ξ))
    (hClosed : ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X},
      IsPullback pZ pX π f → ClosedImmersion pZ) :
    existsFppf f := sorry

/-- `existsFppf f` supplies a representable fppf base change and its closed pullbacks. -/
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

/-- A morphism is a closed immersion exactly when the four locality tests hold. -/
@[stacks 0GHY]
theorem tfae :
    List.TFAE [ClosedImmersion f, forallScheme f, forallAffine f,
      existsCoverOnTarget f, existsFppf f] := sorry

/-- Closed immersion is equivalent to the scheme-valued base-change test. -/
theorem iff_forallScheme : ClosedImmersion f ↔ forallScheme f := sorry

/-- Closed immersion is equivalent to the affine base-change test. -/
theorem iff_forallAffine : ClosedImmersion f ↔ forallAffine f := sorry

/-- Closed immersion is equivalent to the covering-family test. -/
theorem iff_existsCoverOnTarget : ClosedImmersion f ↔ existsCoverOnTarget f := sorry

/-- Closed immersion is equivalent to the representable fppf base-change test. -/
theorem iff_existsFppf : ClosedImmersion f ↔ existsFppf f := sorry

end ClosedImmersion

end AlgebraicGeometry.FormalAlgebraicSpace
