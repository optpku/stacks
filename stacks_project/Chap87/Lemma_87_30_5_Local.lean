module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap87.Definition_87_30_1_Separation
public import stacks_project.Chap87.Lemma_87_20_11_InfinitesimalStages
public import stacks_project.Chap88.Definition_88_20_1_Etale
public import stacks_project.Chap88.Definition_88_21_1_Formal

/-!
# Local tests for separation axioms of morphisms of formal algebraic spaces

Separated and quasi-separated morphisms of functors of points may be tested on
scheme-valued and affine base change, on the absolute separation of the
reduction of an affine-scheme-valued fibre product, and on a Definition
87.11.1 étale atlas of the target by affine formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Separated

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)

/-- The projection of every scheme-valued base change of `f` is separated. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Separated pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is
separated. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Separated pZ := sorry

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Separated pZ) : forallScheme f := sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
separated. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Separated pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is separated whenever `forallScheme f` holds. -/
theorem pullback_snd {Z : Over S} (h : forallScheme f) (g : yoneda.obj Z ⟶ Y)
    [HasPullback f g] : Separated (pullback.snd f g) := sorry

end forallScheme

/-- The projection of every affine-scheme-valued base change of `f` is
separated. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Separated pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is separated. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Separated pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Separated pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is separated. -/
theorem spec (h : forallAffine f) {Z : Over S}
    [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Separated pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is separated whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    (h : forallAffine f) (g : yoneda.obj Z ⟶ Y) [HasPullback f g] :
    Separated (pullback.snd f g) := sorry

end forallAffine

/-- Every affine-scheme-valued fibre product of `f` is a separated formal
algebraic space in the sense of Definition 87.16.3: its reduction is an
absolutely separated algebraic space. -/
def forallAffineSpace : Prop :=
  ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] [Reduction P],
    IsPullback pZ pX g f → AlgebraicSpace.IsAbsolutelySeparated (reduction P)

/-- `forallAffineSpace f` means every affine-scheme-valued fibre product of `f`
has absolutely separated reduction. -/
theorem forallAffineSpace_iff : forallAffineSpace f ↔
    ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X)
      [IsFormalAlgebraicSpace P] [Reduction P],
      IsPullback pZ pX g f →
        AlgebraicSpace.IsAbsolutelySeparated (reduction P) := sorry

namespace forallAffineSpace

/-- Affine-scheme-valued fibre products whose reductions are absolutely
separated witness `forallAffineSpace f`. -/
theorem of (h : ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] [Reduction P],
    IsPullback pZ pX g f →
      AlgebraicSpace.IsAbsolutelySeparated (reduction P)) :
    forallAffineSpace f := sorry

/-- Under `forallAffineSpace f`, the reduction of any affine-scheme-valued
fibre product of `f` is absolutely separated. -/
theorem spec (h : forallAffineSpace f) {Z : Over S}
    [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] [Reduction P]
    (sq : IsPullback pZ pX g f) :
    AlgebraicSpace.IsAbsolutelySeparated (reduction P) := sorry

/-- The reduction of the chosen fibre product along a morphism from an affine
scheme is absolutely separated whenever `forallAffineSpace f` holds. -/
theorem pullback_snd {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    (h : forallAffineSpace f) (g : yoneda.obj Z ⟶ Y) [HasPullback f g]
    [IsFormalAlgebraicSpace (pullback f g)] [Reduction (pullback f g)] :
    AlgebraicSpace.IsAbsolutelySeparated (reduction (pullback f g)) := sorry

end forallAffineSpace

/-- There is a Definition 87.11.1 covering of `Y` by affine formal algebraic
spaces, étale and jointly fppf-locally surjective, along which every pullback
of `f` is separated. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
    (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
      (∀ j, Etale (π j)) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) ∧
          (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
            IsPullback pY pX (π j) f → Separated pY)

/-- `existsCoverOnTarget f` is the existence of a Definition 87.11.1 atlas of
`Y` along which pullbacks of `f` are separated. -/
theorem existsCoverOnTarget_iff : existsCoverOnTarget f ↔
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (sigmaDesc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
              IsPullback pY pX (π j) f → Separated pY) := sorry

namespace existsCoverOnTarget

/-- A Definition 87.11.1 atlas of `Y` with separated pullbacks of `f` witnesses
`existsCoverOnTarget f`. -/
theorem of {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : (j : ι) → Y_ j ⟶ Y)
    (hAffine : ∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j))
    (hEtale : ∀ j, Etale (π j))
    (hCover : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (sigmaDesc π))
    (hSep : ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
      IsPullback pY pX (π j) f → Separated pY) :
    existsCoverOnTarget f := sorry

/-- `existsCoverOnTarget f` supplies a Definition 87.11.1 atlas of `Y` along
which pullbacks of `f` are separated. -/
theorem spec (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (sigmaDesc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
              IsPullback pY pX (π j) f → Separated pY) := sorry

end existsCoverOnTarget

end Separated

namespace QuasiSeparated

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)

/-- The projection of every scheme-valued base change of `f` is
quasi-separated. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → QuasiSeparated pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is
quasi-separated. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → QuasiSeparated pZ := sorry

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → QuasiSeparated pZ) : forallScheme f := sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
quasi-separated. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : QuasiSeparated pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is quasi-separated whenever `forallScheme f` holds. -/
theorem pullback_snd {Z : Over S} (h : forallScheme f) (g : yoneda.obj Z ⟶ Y)
    [HasPullback f g] : QuasiSeparated (pullback.snd f g) := sorry

end forallScheme

/-- The projection of every affine-scheme-valued base change of `f` is
quasi-separated. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → QuasiSeparated pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is quasi-separated. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → QuasiSeparated pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → QuasiSeparated pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is quasi-separated. -/
theorem spec (h : forallAffine f) {Z : Over S}
    [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : QuasiSeparated pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is quasi-separated whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    (h : forallAffine f) (g : yoneda.obj Z ⟶ Y) [HasPullback f g] :
    QuasiSeparated (pullback.snd f g) := sorry

end forallAffine

/-- Every affine-scheme-valued fibre product of `f` is a quasi-separated formal
algebraic space in the sense of Definition 87.16.3: its reduction is an
absolutely quasi-separated algebraic space. -/
def forallAffineSpace : Prop :=
  ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] [Reduction P],
    IsPullback pZ pX g f →
      AlgebraicSpace.IsAbsolutelyQuasiSeparated (reduction P)

/-- `forallAffineSpace f` means every affine-scheme-valued fibre product of `f`
has absolutely quasi-separated reduction. -/
theorem forallAffineSpace_iff : forallAffineSpace f ↔
    ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X)
      [IsFormalAlgebraicSpace P] [Reduction P],
      IsPullback pZ pX g f →
        AlgebraicSpace.IsAbsolutelyQuasiSeparated (reduction P) := sorry

namespace forallAffineSpace

/-- Affine-scheme-valued fibre products whose reductions are absolutely
quasi-separated witness `forallAffineSpace f`. -/
theorem of (h : ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] [Reduction P],
    IsPullback pZ pX g f →
      AlgebraicSpace.IsAbsolutelyQuasiSeparated (reduction P)) :
    forallAffineSpace f := sorry

/-- Under `forallAffineSpace f`, the reduction of any affine-scheme-valued
fibre product of `f` is absolutely quasi-separated. -/
theorem spec (h : forallAffineSpace f) {Z : Over S}
    [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] [Reduction P]
    (sq : IsPullback pZ pX g f) :
    AlgebraicSpace.IsAbsolutelyQuasiSeparated (reduction P) := sorry

/-- The reduction of the chosen fibre product along a morphism from an affine
scheme is absolutely quasi-separated whenever `forallAffineSpace f` holds. -/
theorem pullback_snd {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    (h : forallAffineSpace f) (g : yoneda.obj Z ⟶ Y) [HasPullback f g]
    [IsFormalAlgebraicSpace (pullback f g)] [Reduction (pullback f g)] :
    AlgebraicSpace.IsAbsolutelyQuasiSeparated (reduction (pullback f g)) := sorry

end forallAffineSpace

/-- There is a Definition 87.11.1 covering of `Y` by affine formal algebraic
spaces, étale and jointly fppf-locally surjective, along which every pullback
of `f` is quasi-separated. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
    (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
      (∀ j, Etale (π j)) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) ∧
          (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
            IsPullback pY pX (π j) f → QuasiSeparated pY)

/-- `existsCoverOnTarget f` is the existence of a Definition 87.11.1 atlas of
`Y` along which pullbacks of `f` are quasi-separated. -/
theorem existsCoverOnTarget_iff : existsCoverOnTarget f ↔
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (sigmaDesc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
              IsPullback pY pX (π j) f → QuasiSeparated pY) := sorry

namespace existsCoverOnTarget

/-- A Definition 87.11.1 atlas of `Y` with quasi-separated pullbacks of `f`
witnesses `existsCoverOnTarget f`. -/
theorem of {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : (j : ι) → Y_ j ⟶ Y)
    (hAffine : ∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j))
    (hEtale : ∀ j, Etale (π j))
    (hCover : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (sigmaDesc π))
    (hQS : ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
      IsPullback pY pX (π j) f → QuasiSeparated pY) :
    existsCoverOnTarget f := sorry

/-- `existsCoverOnTarget f` supplies a Definition 87.11.1 atlas of `Y` along
which pullbacks of `f` are quasi-separated. -/
theorem spec (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (sigmaDesc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
              IsPullback pY pX (π j) f → QuasiSeparated pY) := sorry

end existsCoverOnTarget

end QuasiSeparated

end AlgebraicGeometry.FormalAlgebraicSpace
