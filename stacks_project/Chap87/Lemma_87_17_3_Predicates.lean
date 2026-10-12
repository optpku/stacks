/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

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
public import stacks_project.Chap87.Lemma_87_17_3_QuasiCompact
public import stacks_project.Chap88.Definition_88_20_1_Etale

/-!
# Local tests for quasi-compactness of morphisms of formal algebraic spaces

Quasi-compactness of a morphism of formal algebraic spaces may be tested on
quasi-compact and affine scheme-valued base change, and on a Definition
87.11.1 étale atlas of the target by affine formal algebraic spaces, by asking
that the fibre-product vertices be quasi-compact formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y)

/-- Every fibre product of `f` along a morphism from a quasi-compact scheme is
a quasi-compact formal algebraic space. -/
def forallQuasiCompactScheme : Prop :=
  ∀ {T : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
    {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X}
    [CompactSpace T.left] [IsFormalAlgebraicSpace P] [Reduction P],
    IsPullback pT pX g f → IsQuasiCompact P

/-- `forallQuasiCompactScheme f` means every quasi-compact scheme-valued
pullback vertex of `f` is a quasi-compact formal algebraic space. -/
theorem forallQuasiCompactScheme_iff : forallQuasiCompactScheme f ↔
    ∀ (T : Over S) (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj T ⟶ Y)
      (pT : P ⟶ yoneda.obj T) (pX : P ⟶ X)
      [CompactSpace T.left] [IsFormalAlgebraicSpace P] [Reduction P],
      IsPullback pT pX g f → IsQuasiCompact P :=
  sorry

namespace forallQuasiCompactScheme

/-- A universal quasi-compact scheme-valued pullback condition witnesses
`forallQuasiCompactScheme f`. -/
theorem of
    (h : ∀ {T : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
      {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X}
      [CompactSpace T.left] [IsFormalAlgebraicSpace P] [Reduction P],
      IsPullback pT pX g f → IsQuasiCompact P) :
    forallQuasiCompactScheme f :=
  sorry

/-- Under `forallQuasiCompactScheme f`, the vertex of any quasi-compact
scheme-valued pullback of `f` is a quasi-compact formal algebraic space. -/
theorem spec (h : forallQuasiCompactScheme f) {T : Over S}
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
    {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X}
    [CompactSpace T.left] [IsFormalAlgebraicSpace P] [Reduction P]
    (sq : IsPullback pT pX g f) : IsQuasiCompact P :=
  sorry

/-- The chosen pullback `pullback f g` along a morphism from a quasi-compact
scheme is a quasi-compact formal algebraic space whenever
`forallQuasiCompactScheme f` holds. -/
theorem pullback_snd {T : Over S} [CompactSpace T.left]
    (h : forallQuasiCompactScheme f) (g : yoneda.obj T ⟶ Y) [HasPullback f g]
    [IsFormalAlgebraicSpace (pullback f g)] [Reduction (pullback f g)] :
    IsQuasiCompact (pullback f g) :=
  sorry

end forallQuasiCompactScheme

/-- Every fibre product of `f` along a morphism from an affine scheme is a
quasi-compact formal algebraic space. -/
def forallAffine : Prop :=
  ∀ {T : Over S} [AlgebraicGeometry.IsAffine T.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
    {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] [Reduction P],
    IsPullback pT pX g f → IsQuasiCompact P

/-- `forallAffine f` means every affine-scheme-valued pullback vertex of `f` is
a quasi-compact formal algebraic space. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (T : Over S) [AlgebraicGeometry.IsAffine T.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj T ⟶ Y)
      (pT : P ⟶ yoneda.obj T) (pX : P ⟶ X)
      [IsFormalAlgebraicSpace P] [Reduction P],
      IsPullback pT pX g f → IsQuasiCompact P :=
  sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {T : Over S} [AlgebraicGeometry.IsAffine T.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
    {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] [Reduction P],
    IsPullback pT pX g f → IsQuasiCompact P) : forallAffine f :=
  sorry

/-- Under `forallAffine f`, the vertex of any affine-scheme-valued pullback of
`f` is a quasi-compact formal algebraic space. -/
theorem spec (h : forallAffine f) {T : Over S}
    [AlgebraicGeometry.IsAffine T.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj T ⟶ Y} {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] [Reduction P]
    (sq : IsPullback pT pX g f) : IsQuasiCompact P :=
  sorry

/-- The chosen pullback `pullback f g` along a morphism from an affine scheme
is a quasi-compact formal algebraic space whenever `forallAffine f` holds. -/
theorem pullback_snd {T : Over S} [AlgebraicGeometry.IsAffine T.left]
    (h : forallAffine f) (g : yoneda.obj T ⟶ Y) [HasPullback f g]
    [IsFormalAlgebraicSpace (pullback f g)] [Reduction (pullback f g)] :
    IsQuasiCompact (pullback f g) :=
  sorry

end forallAffine

/-- There is a Definition 87.11.1 covering of `Y` by affine formal algebraic
spaces, étale and jointly fppf-locally surjective, along which every pullback
vertex of `f` is a quasi-compact formal algebraic space. -/
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
            IsPullback pY pX (π j) f → IsQuasiCompact P)

/-- `existsCoverOnTarget f` is the existence of a Definition 87.11.1 atlas of
`Y` along which pullback vertices of `f` are quasi-compact formal algebraic
spaces. -/
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
              IsPullback pY pX (π j) f → IsQuasiCompact P) :=
  sorry

namespace existsCoverOnTarget

/-- A Definition 87.11.1 atlas of `Y` with quasi-compact pullback vertices of
`f` witnesses `existsCoverOnTarget f`. -/
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
    (hQC : ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X}
      [IsFormalAlgebraicSpace (Y_ j)] [IsFormalAlgebraicSpace P]
      [Reduction (Y_ j)] [Reduction P],
      IsPullback pY pX (π j) f → IsQuasiCompact P) :
    existsCoverOnTarget f :=
  sorry

/-- `existsCoverOnTarget f` supplies a Definition 87.11.1 atlas of `Y` along
which pullback vertices of `f` are quasi-compact formal algebraic spaces. -/
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
              IsPullback pY pX (π j) f → IsQuasiCompact P) :=
  sorry

end existsCoverOnTarget

end AlgebraicGeometry.FormalAlgebraicSpace
