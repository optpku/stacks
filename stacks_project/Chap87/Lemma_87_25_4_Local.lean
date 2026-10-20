/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap87.FormalAlgebraicSpace.Yoneda

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Order.Directed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap87.Definition_87_25_1_Surjective
public import stacks_project.Chap88.Definition_88_20_1_Etale

/-!
# Local tests for surjective morphisms of formal algebraic spaces

Surjective morphisms of functors of points may be tested on scheme-valued and
affine base change, on a Definition 87.11.1 étale atlas of the target by affine
formal algebraic spaces, and on some surjective morphism of formal algebraic
spaces to the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Surjective

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y)

/-- The projection of every scheme-valued base change of `f` is surjective. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] [Reduction (yoneda.obj Z)] [Reduction P],
    IsPullback pZ pX g f → Surjective pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is
surjective. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X)
      [IsFormalAlgebraicSpace P] [Reduction (yoneda.obj Z)] [Reduction P],
      IsPullback pZ pX g f → Surjective pZ := sorry

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] [Reduction (yoneda.obj Z)] [Reduction P],
    IsPullback pZ pX g f → Surjective pZ) : forallScheme f := sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
surjective. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] [Reduction (yoneda.obj Z)] [Reduction P]
    (sq : IsPullback pZ pX g f) : Surjective pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is surjective whenever `forallScheme f` holds. -/
theorem pullback_snd {Z : Over S} [Reduction (yoneda.obj Z)]
    (h : forallScheme f) (g : yoneda.obj Z ⟶ Y) [HasPullback f g]
    [IsFormalAlgebraicSpace (pullback f g)] [Reduction (pullback f g)] :
    Surjective (pullback.snd f g) := sorry

end forallScheme

/-- The projection of every affine-scheme-valued base change of `f` is
surjective. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] [Reduction (yoneda.obj Z)] [Reduction P],
    IsPullback pZ pX g f → Surjective pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is surjective. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X)
      [IsFormalAlgebraicSpace P] [Reduction (yoneda.obj Z)] [Reduction P],
      IsPullback pZ pX g f → Surjective pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] [Reduction (yoneda.obj Z)] [Reduction P],
    IsPullback pZ pX g f → Surjective pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is surjective. -/
theorem spec (h : forallAffine f) {Z : Over S}
    [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] [Reduction (yoneda.obj Z)] [Reduction P]
    (sq : IsPullback pZ pX g f) : Surjective pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is surjective whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    [Reduction (yoneda.obj Z)] (h : forallAffine f) (g : yoneda.obj Z ⟶ Y)
    [HasPullback f g] [IsFormalAlgebraicSpace (pullback f g)]
    [Reduction (pullback f g)] : Surjective (pullback.snd f g) := sorry

end forallAffine

/-- There is a Definition 87.11.1 covering of `Y` by affine formal algebraic
spaces, étale and jointly fppf-locally surjective, along which every pullback
of `f` is surjective. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
    (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S),
      (∀ i, AlgebraicGeometry.IsAffine (D.obj i).left) ∧
        (∀ {i k : Λ} (φ : i ⟶ k), AlgebraicGeometry.IsThickening (D.map φ).left) ∧
          Presheaf.IsSheaf (Scheme.fppfTopology.over S) (Y_ j) ∧
            ∃ (c : Cocone (D ⋙ yoneda)) (η : c.pt ⟶ Y_ j),
              Nonempty (IsColimit c) ∧
                Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η ∧
                  Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η) ∧
      (∀ j, Etale (π j)) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (Limits.Sigma.desc π) ∧
          (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X}
            [IsFormalAlgebraicSpace (Y_ j)] [IsFormalAlgebraicSpace P]
            [Reduction (Y_ j)] [Reduction P],
            IsPullback pY pX (π j) f → Surjective pY)

/-- `existsCoverOnTarget f` is the existence of a Definition 87.11.1 atlas of
`Y` along which pullbacks of `f` are surjective. -/
theorem existsCoverOnTarget_iff : existsCoverOnTarget f ↔
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S),
        (∀ i, AlgebraicGeometry.IsAffine (D.obj i).left) ∧
          (∀ {i k : Λ} (φ : i ⟶ k),
            AlgebraicGeometry.IsThickening (D.map φ).left) ∧
            Presheaf.IsSheaf (Scheme.fppfTopology.over S) (Y_ j) ∧
              ∃ (c : Cocone (D ⋙ yoneda)) (η : c.pt ⟶ Y_ j),
                Nonempty (IsColimit c) ∧
                  Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η ∧
                    Presheaf.IsLocallyInjective
                      (Scheme.fppfTopology.over S) η) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
              (Limits.Sigma.desc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X}
              [IsFormalAlgebraicSpace (Y_ j)] [IsFormalAlgebraicSpace P]
              [Reduction (Y_ j)] [Reduction P],
              IsPullback pY pX (π j) f → Surjective pY) := sorry

namespace existsCoverOnTarget

/-- A Definition 87.11.1 atlas of `Y` with surjective pullbacks of `f` witnesses
`existsCoverOnTarget f`. -/
theorem of {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : (j : ι) → Y_ j ⟶ Y)
    (hAffine : ∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S),
      (∀ i, AlgebraicGeometry.IsAffine (D.obj i).left) ∧
        (∀ {i k : Λ} (φ : i ⟶ k), AlgebraicGeometry.IsThickening (D.map φ).left) ∧
          Presheaf.IsSheaf (Scheme.fppfTopology.over S) (Y_ j) ∧
            ∃ (c : Cocone (D ⋙ yoneda)) (η : c.pt ⟶ Y_ j),
              Nonempty (IsColimit c) ∧
                Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η ∧
                  Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η)
    (hEtale : ∀ j, Etale (π j))
    (hCover : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (Limits.Sigma.desc π))
    (hSurj : ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X}
      [IsFormalAlgebraicSpace (Y_ j)] [IsFormalAlgebraicSpace P]
      [Reduction (Y_ j)] [Reduction P],
      IsPullback pY pX (π j) f → Surjective pY) :
    existsCoverOnTarget f := sorry

/-- `existsCoverOnTarget f` supplies a Definition 87.11.1 atlas of `Y` along
which pullbacks of `f` are surjective. -/
theorem spec (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S),
        (∀ i, AlgebraicGeometry.IsAffine (D.obj i).left) ∧
          (∀ {i k : Λ} (φ : i ⟶ k),
            AlgebraicGeometry.IsThickening (D.map φ).left) ∧
            Presheaf.IsSheaf (Scheme.fppfTopology.over S) (Y_ j) ∧
              ∃ (c : Cocone (D ⋙ yoneda)) (η : c.pt ⟶ Y_ j),
                Nonempty (IsColimit c) ∧
                  Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η ∧
                    Presheaf.IsLocallyInjective
                      (Scheme.fppfTopology.over S) η) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
              (Limits.Sigma.desc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X}
              [IsFormalAlgebraicSpace (Y_ j)] [IsFormalAlgebraicSpace P]
              [Reduction (Y_ j)] [Reduction P],
              IsPullback pY pX (π j) f → Surjective pY) := sorry

end existsCoverOnTarget

/-- There is a surjective morphism of formal algebraic spaces to `Y` along
which every pullback of `f` is surjective. -/
def existsSurjectiveOnTarget : Prop :=
  ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (hZ : IsFormalAlgebraicSpace Z)
    (hR : @Reduction S Z hZ) (g : Z ⟶ Y),
    @Surjective S Z Y hZ _ hR _ g ∧
      ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X}
        (hP : IsFormalAlgebraicSpace P) (hRP : @Reduction S P hP),
        IsPullback pZ pX g f → @Surjective S P Z hP hZ hRP hR pZ

/-- `existsSurjectiveOnTarget f` is the existence of a surjective morphism of
formal algebraic spaces to `Y` along which pullbacks of `f` are surjective. -/
theorem existsSurjectiveOnTarget_iff : existsSurjectiveOnTarget f ↔
    ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (hZ : IsFormalAlgebraicSpace Z)
      (hR : @Reduction S Z hZ) (g : Z ⟶ Y),
      @Surjective S Z Y hZ _ hR _ g ∧
        ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X}
          (hP : IsFormalAlgebraicSpace P) (hRP : @Reduction S P hP),
          IsPullback pZ pX g f → @Surjective S P Z hP hZ hRP hR pZ := sorry

namespace existsSurjectiveOnTarget

/-- A surjective morphism of formal algebraic spaces to `Y` with surjective
pullbacks of `f` witnesses `existsSurjectiveOnTarget f`. -/
theorem of {Z : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace Z] [Reduction Z]
    (g : Z ⟶ Y) [Surjective g]
    (h : ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X}
      [IsFormalAlgebraicSpace P] [Reduction P],
      IsPullback pZ pX g f → Surjective pZ) :
    existsSurjectiveOnTarget f := sorry

/-- `existsSurjectiveOnTarget f` supplies a surjective morphism of formal
algebraic spaces to `Y` along which pullbacks of `f` are surjective. -/
theorem spec (h : existsSurjectiveOnTarget f) :
    ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (hZ : IsFormalAlgebraicSpace Z)
      (hR : @Reduction S Z hZ) (g : Z ⟶ Y),
      @Surjective S Z Y hZ _ hR _ g ∧
        ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X}
          (hP : IsFormalAlgebraicSpace P) (hRP : @Reduction S P hP),
          IsPullback pZ pX g f → @Surjective S P Z hP hZ hRP hR pZ := sorry

end existsSurjectiveOnTarget

end Surjective

end AlgebraicGeometry.FormalAlgebraicSpace
