module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap80.Definition_80_4_1_Relative
public import stacks_project.Chap88.Definition_88_16_1_Affine
public import stacks_project.Chap88.Definition_88_20_1_Etale

/-!
# Characterizations of monomorphisms of formal algebraic spaces

Monomorphisms of functors of points may be tested on scheme-valued and affine
base change, on a Definition 87.11.1 étale atlas of the target, on a jointly
fppf-locally surjective family, and on a representable fppf morphism of formal
algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Monomorphisms

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}

/-- A morphism of functors of points is representable by algebraic spaces,
surjective, flat, and locally of finite presentation when the Bootstrap
transfer of those algebraic-space properties holds. -/
def representableFppf (g : X ⟶ Y) : Prop :=
  AlgebraicSpace.relativeAlgebraicSpaces
    (fun _ _ h ↦ AlgebraicSpace.Surjective h ∧ AlgebraicSpace.Flat h ∧
      AlgebraicSpace.LocallyOfFinitePresentation h) g

/-- `representableFppf g` means `g` is representable by algebraic spaces and
every scheme Yoneda pullback is surjective, flat, and locally of finite
presentation. -/
theorem representableFppf_iff (g : X ⟶ Y) :
    representableFppf g ↔
      AlgebraicSpace.representableByAlgebraicSpaces g ∧
        ∀ (hg : AlgebraicSpace.representableByAlgebraicSpaces g) ⦃U : Over S⦄
          (ξ : yoneda.obj U ⟶ Y),
          AlgebraicSpace.Surjective (hg.pullbackHom ξ) ∧
            AlgebraicSpace.Flat (hg.pullbackHom ξ) ∧
              AlgebraicSpace.LocallyOfFinitePresentation (hg.pullbackHom ξ) :=
  sorry

namespace representableFppf

/-- A morphism representable by algebraic spaces whose scheme Yoneda pullbacks
are surjective, flat, and locally of finite presentation witnesses
`representableFppf`. -/
theorem of {g : X ⟶ Y} (hg : AlgebraicSpace.representableByAlgebraicSpaces g)
    (h : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ Y),
      AlgebraicSpace.Surjective (hg.pullbackHom ξ) ∧
        AlgebraicSpace.Flat (hg.pullbackHom ξ) ∧
          AlgebraicSpace.LocallyOfFinitePresentation (hg.pullbackHom ξ)) :
    representableFppf g :=
  sorry

/-- `representableFppf g` supplies representability by algebraic spaces together
with surjectivity, flatness, and local finite presentation of every scheme
Yoneda pullback. -/
theorem spec {g : X ⟶ Y} (h : representableFppf g) :
    AlgebraicSpace.representableByAlgebraicSpaces g ∧
      ∀ (hg : AlgebraicSpace.representableByAlgebraicSpaces g) ⦃U : Over S⦄
        (ξ : yoneda.obj U ⟶ Y),
        AlgebraicSpace.Surjective (hg.pullbackHom ξ) ∧
          AlgebraicSpace.Flat (hg.pullbackHom ξ) ∧
            AlgebraicSpace.LocallyOfFinitePresentation (hg.pullbackHom ξ) :=
  sorry

end representableFppf

variable [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)

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
  sorry

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Mono pZ) : forallScheme f :=
  sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
a monomorphism. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Mono pZ :=
  sorry

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
  sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Mono pZ) : forallAffine f :=
  sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is a monomorphism. -/
theorem spec (h : forallAffine f) {Z : Over S}
    [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Mono pZ :=
  sorry

end forallAffine

/-- There is a Definition 87.11.1 covering of `Y` by affine formal algebraic
spaces, étale and jointly fppf-locally surjective, along which every pullback
of `f` is a monomorphism. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
    (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
      (∀ j, Etale (π j)) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) ∧
          (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
            IsPullback pY pX (π j) f → Mono pY)

/-- `existsCoverOnTarget f` is the existence of a Definition 87.11.1 atlas of
`Y` along which pullbacks of `f` are monomorphisms. -/
theorem existsCoverOnTarget_iff : existsCoverOnTarget f ↔
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (sigmaDesc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
              IsPullback pY pX (π j) f → Mono pY) :=
  sorry

namespace existsCoverOnTarget

/-- A Definition 87.11.1 atlas of `Y` with monomorphic pullbacks of `f`
witnesses `existsCoverOnTarget f`. -/
theorem of {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : (j : ι) → Y_ j ⟶ Y)
    (hAffine : ∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j))
    (hEtale : ∀ j, Etale (π j))
    (hCover : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (sigmaDesc π))
    (hMono : ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
      IsPullback pY pX (π j) f → Mono pY) :
    existsCoverOnTarget f :=
  sorry

/-- `existsCoverOnTarget f` supplies a Definition 87.11.1 atlas of `Y` along
which pullbacks of `f` are monomorphisms. -/
theorem spec (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (sigmaDesc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
              IsPullback pY pX (π j) f → Mono pY) :=
  sorry

end existsCoverOnTarget

/-- There is a family of morphisms to `Y` whose coproduct is an fppf sheaf
surjection, along which every pullback of `f` is a monomorphism. -/
def existsSheafSurjection : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) ∧
      ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
        IsPullback pY pX (π j) f → Mono pY

/-- `existsSheafSurjection f` is the existence of a jointly fppf-locally
surjective family along which pullbacks of `f` are monomorphisms. -/
theorem existsSheafSurjection_iff : existsSheafSurjection f ↔
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) ∧
        ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
          IsPullback pY pX (π j) f → Mono pY :=
  sorry

namespace existsSheafSurjection

/-- A jointly fppf-locally surjective family with monomorphic pullbacks of `f`
witnesses `existsSheafSurjection f`. -/
theorem of {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : (j : ι) → Y_ j ⟶ Y)
    (hCover : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (sigmaDesc π))
    (hMono : ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
      IsPullback pY pX (π j) f → Mono pY) :
    existsSheafSurjection f :=
  sorry

/-- `existsSheafSurjection f` supplies a jointly fppf-locally surjective family
along which pullbacks of `f` are monomorphisms. -/
theorem spec (h : existsSheafSurjection f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) ∧
        ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
          IsPullback pY pX (π j) f → Mono pY :=
  sorry

end existsSheafSurjection

/-- There is a morphism of formal algebraic spaces to `Y`, representable by
algebraic spaces, surjective, flat, and locally of finite presentation, along
which every pullback of `f` is a monomorphism. -/
def existsFppf : Prop :=
  ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (_ : IsFormalAlgebraicSpace Z) (g : Z ⟶ Y),
    representableFppf g ∧
      ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X},
        IsPullback pZ pX g f → Mono pZ

/-- `existsFppf f` is the existence of a representable fppf morphism of formal
algebraic spaces to `Y` along which pullbacks of `f` are monomorphisms. -/
theorem existsFppf_iff : existsFppf f ↔
    ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (_ : IsFormalAlgebraicSpace Z) (g : Z ⟶ Y),
      representableFppf g ∧
        ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X},
          IsPullback pZ pX g f → Mono pZ :=
  sorry

namespace existsFppf

/-- A representable fppf morphism of formal algebraic spaces to `Y` with
monomorphic pullbacks of `f` witnesses `existsFppf f`. -/
theorem of {Z : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace Z] (g : Z ⟶ Y)
    (hg : representableFppf g)
    (hMono : ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X},
      IsPullback pZ pX g f → Mono pZ) :
    existsFppf f :=
  sorry

/-- `existsFppf f` supplies a representable fppf morphism of formal algebraic
spaces to `Y` along which pullbacks of `f` are monomorphisms. -/
theorem spec (h : existsFppf f) :
    ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (_ : IsFormalAlgebraicSpace Z) (g : Z ⟶ Y),
      representableFppf g ∧
        ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X},
          IsPullback pZ pX g f → Mono pZ :=
  sorry

end existsFppf

end Monomorphisms

end AlgebraicGeometry.FormalAlgebraicSpace
