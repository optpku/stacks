/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleCover
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Fppf

/-!
# Local tests for monomorphisms of formal algebraic spaces

Monicity can be detected by scheme and affine scheme base changes, affine
étale covers, surjective families of sheaves, or representable fppf covers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.Monomorphisms

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}

variable (f : X ⟶ Y)

/-- The projection of every scheme-valued base change of `f` is a
monomorphism. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Mono pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is a
monomorphism. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Mono pZ :=
  Iff.rfl

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Mono pZ) : forallScheme f :=
  h

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
a monomorphism. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Mono pZ :=
  h sq

end forallScheme

/-- The projection of every affine-scheme-valued base change of `f` is a
monomorphism. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Mono pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is a monomorphism. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Mono pZ :=
  Iff.rfl

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Mono pZ) : forallAffine f :=
  h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is a monomorphism. -/
theorem spec (h : forallAffine f) {Z : Over S}
    [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Mono pZ :=
  h sq

end forallAffine

/-- There is an affine étale cover of the target along which every pullback
projection is a monomorphism. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
    IsEtaleAffineCover π ∧
      ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
        IsPullback pY pX (π j) f → Mono pY

/-- The affine étale cover test is equivalent to the existence of an explicit
covering family with monomorphic pullback projections. -/
theorem existsCoverOnTarget_iff : existsCoverOnTarget f ↔
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      IsEtaleAffineCover π ∧
        ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
          IsPullback pY pX (π j) f → Mono pY :=
  Iff.rfl

namespace existsCoverOnTarget

/-- An affine étale covering family with monomorphic pullback projections
satisfies the affine étale cover test. -/
theorem of {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : (j : ι) → Y_ j ⟶ Y) (hCover : IsEtaleAffineCover π)
    (hMono : ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
      IsPullback pY pX (π j) f → Mono pY) :
    existsCoverOnTarget f :=
  ⟨ι, Y_, π, hCover, hMono⟩

/-- The affine étale cover test supplies a covering family with monomorphic
pullback projections. -/
theorem spec (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      IsEtaleAffineCover π ∧
        ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
          IsPullback pY pX (π j) f → Mono pY :=
  h

end existsCoverOnTarget

/-- There is a family of fppf sheaves mapping to `Y` whose coproduct is a sheaf
surjection, along which every pullback of `f` is a monomorphism. -/
def existsSheafSurjection : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
    (∀ j, Presheaf.IsSheaf (Scheme.fppfTopology.over S) (Y_ j)) ∧
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) ∧
        ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
          IsPullback pY pX (π j) f → Mono pY

/-- `existsSheafSurjection f` is the existence of a jointly fppf-locally
surjective family of fppf sheaves along which pullbacks of `f` are
monomorphisms. -/
theorem existsSheafSurjection_iff : existsSheafSurjection f ↔
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, Presheaf.IsSheaf (Scheme.fppfTopology.over S) (Y_ j)) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) ∧
        ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
          IsPullback pY pX (π j) f → Mono pY :=
  Iff.rfl

namespace existsSheafSurjection

/-- A jointly fppf-locally surjective family of fppf sheaves with monomorphic
pullbacks of `f` witnesses `existsSheafSurjection f`. -/
theorem of {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : (j : ι) → Y_ j ⟶ Y)
    (hSheaf : ∀ j, Presheaf.IsSheaf (Scheme.fppfTopology.over S) (Y_ j))
    (hCover : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (sigmaDesc π))
    (hMono : ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
      IsPullback pY pX (π j) f → Mono pY) :
    existsSheafSurjection f :=
  ⟨ι, Y_, π, hSheaf, hCover, hMono⟩

/-- `existsSheafSurjection f` supplies a jointly fppf-locally surjective family
of fppf sheaves along which pullbacks of `f` are monomorphisms. -/
theorem spec (h : existsSheafSurjection f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, Presheaf.IsSheaf (Scheme.fppfTopology.over S) (Y_ j)) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) ∧
        ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
          IsPullback pY pX (π j) f → Mono pY :=
  h

end existsSheafSurjection

/-- There is a morphism of formal algebraic spaces to `Y`, representable by
algebraic spaces, surjective, flat, and locally of finite presentation, along
which every pullback of `f` is a monomorphism. -/
def existsFppf : Prop :=
  ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (_ : IsFormalAlgebraicSpace Z) (g : Z ⟶ Y),
    AlgebraicSpace.representableSurjectiveFppf g ∧
      ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → Mono pZ

/-- `existsFppf f` is the existence of a representable fppf morphism of formal
algebraic spaces to `Y` along which pullbacks of `f` are monomorphisms. -/
theorem existsFppf_iff : existsFppf f ↔
    ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (_ : IsFormalAlgebraicSpace Z) (g : Z ⟶ Y),
      AlgebraicSpace.representableSurjectiveFppf g ∧
        ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X},
          IsPullback pZ pX g f → Mono pZ :=
  Iff.rfl

namespace existsFppf

/-- A representable fppf morphism of formal algebraic spaces to `Y` with
monomorphic pullbacks of `f` witnesses `existsFppf f`. -/
theorem of {Z : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace Z] (g : Z ⟶ Y)
    (hg : AlgebraicSpace.representableSurjectiveFppf g)
    (hMono : ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X},
      IsPullback pZ pX g f → Mono pZ) :
    existsFppf f :=
  ⟨Z, inferInstance, g, hg, hMono⟩

/-- `existsFppf f` supplies a representable fppf morphism of formal algebraic
spaces to `Y` along which pullbacks of `f` are monomorphisms. -/
theorem spec (h : existsFppf f) :
    ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (_ : IsFormalAlgebraicSpace Z) (g : Z ⟶ Y),
      AlgebraicSpace.representableSurjectiveFppf g ∧
        ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X},
          IsPullback pZ pX g f → Mono pZ :=
  h

end existsFppf

/-- For a morphism of formal algebraic spaces, monicity is equivalent to
monicity after every scheme or affine scheme base change, after an affine étale
cover, after a surjective family of fppf sheaves, and after a representable
surjective flat locally finitely presented cover. -/
theorem tfae [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) :
    List.TFAE [Mono f, forallScheme f, forallAffine f, existsCoverOnTarget f,
      existsSheafSurjection f, existsFppf f] :=
  sorry

/-- A morphism of formal algebraic spaces is a monomorphism iff every
scheme-valued base change has monomorphic projection. -/
theorem iff_forallScheme [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) : Mono f ↔ forallScheme f :=
  (tfae f).out 0 1

/-- A morphism of formal algebraic spaces is a monomorphism iff every
affine-scheme-valued base change has monomorphic projection. -/
theorem iff_forallAffine [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) : Mono f ↔ forallAffine f :=
  (tfae f).out 0 2

/-- A morphism of formal algebraic spaces is a monomorphism iff some affine
étale cover of the target has monomorphic pullbacks of `f`. -/
theorem iff_existsCoverOnTarget [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) : Mono f ↔ existsCoverOnTarget f :=
  (tfae f).out 0 3

/-- A morphism of formal algebraic spaces is a monomorphism iff some jointly
fppf-locally surjective family of sheaves has monomorphic pullbacks of `f`. -/
theorem iff_existsSheafSurjection [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) : Mono f ↔ existsSheafSurjection f :=
  (tfae f).out 0 4

/-- A morphism of formal algebraic spaces is a monomorphism iff some
representable fppf morphism of formal algebraic spaces to the target has
monomorphic pullbacks of `f`. -/
theorem iff_existsFppf [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) : Mono f ↔ existsFppf f :=
  (tfae f).out 0 5

end AlgebraicGeometry.FormalAlgebraicSpace.Monomorphisms
