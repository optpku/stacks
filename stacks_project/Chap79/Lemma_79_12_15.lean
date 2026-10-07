module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap65.Lemma_65_16_4_IsAlgebraicSpace
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap79.Lemma_79_12_15_Functor

/-!
# Inclusion of the finite-part functor of pairs containing a section
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePart

/-- Lemma 79.12.15 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `σ : Y ⟶ X` be a section of `f`. The
transformation `t : (X/Y, σ)_fin ⟶ (X/Y)_fin` is representable by open
immersions. -/
@[stacks 04RR]
theorem withSectionι_isOpenImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    (MorphismProperty.over
        (@AlgebraicGeometry.IsOpenImmersion :
          MorphismProperty Scheme.{u})).presheaf
      (withSectionι f σ hσ) :=
  sorry

/-- Lemma 79.12.15 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `σ : Y ⟶ X` be a section of `f`. If `f` is
separated, then `t : (X/Y, σ)_fin ⟶ (X/Y)_fin` is representable by open and
closed immersions. -/
@[stacks 04RR]
theorem withSectionι_isOpenAndClosedImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Separated f] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) :
    (MorphismProperty.over
        ((@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u}) ⊓
          (@AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u}))).presheaf
      (withSectionι f σ hσ) :=
  sorry

/-- If `(X/Y)_fin` is an algebraic space, then so is `(X/Y, σ)_fin`. -/
instance instIsAlgebraicSpace_withSectionFunctor {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsAlgebraicSpace (functor f)]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    IsAlgebraicSpace (withSectionFunctor f σ hσ) :=
  sorry

/-- The inclusion `t` as a morphism of algebraic spaces, when both functors are
algebraic spaces. -/
def withSectionιHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsAlgebraicSpace (functor f)] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) :
    ofIsAlgebraicSpace (withSectionFunctor f σ hσ) ⟶
      ofIsAlgebraicSpace (functor f) :=
  withSectionι f σ hσ

/-- If `(X/Y)_fin` is an algebraic space, then `t` is an open immersion of
algebraic spaces. -/
instance instIsOpenImmersion_withSectionι {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsAlgebraicSpace (functor f)]
    (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y) :
    AlgebraicSpace.IsOpenImmersion (withSectionιHom f σ hσ) :=
  sorry

/-- Lemma 79.12.15 (3): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `σ : Y ⟶ X` be a section of `f`. If
`(X/Y)_fin` is an algebraic space, then `(X/Y, σ)_fin` is an algebraic space
and an open subspace of `(X/Y)_fin`. -/
@[stacks 04RR]
def withSectionOpenSubspace {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsAlgebraicSpace (functor f)] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) :
    OpenSubspace (ofIsAlgebraicSpace (functor f)) :=
  OpenSubspace.ofι (withSectionιHom f σ hσ)

/-- The underlying algebraic space of the open subspace is `(X/Y, σ)_fin`. -/
theorem withSectionOpenSubspace_X {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsAlgebraicSpace (functor f)] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) :
    (withSectionOpenSubspace f σ hσ).X =
      ofIsAlgebraicSpace (withSectionFunctor f σ hσ) :=
  sorry

/-- The inclusion of the open subspace is `withSectionιHom`. -/
theorem withSectionOpenSubspace_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsAlgebraicSpace (functor f)] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) :
    (withSectionOpenSubspace f σ hσ).ι = withSectionιHom f σ hσ :=
  sorry

/-- If `(X/Y)_fin` is representable, then so is `(X/Y, σ)_fin`. -/
instance instIsRepresentable_withSectionFunctor {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Functor.IsRepresentable (functor f)] (σ : Y ⟶ X)
    (hσ : σ ≫ f = 𝟙 Y) :
    Functor.IsRepresentable (withSectionFunctor f σ hσ) :=
  sorry

/-- Lemma 79.12.15 (4): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `σ : Y ⟶ X` be a section of `f`. If
`(X/Y)_fin` is a scheme, then `(X/Y, σ)_fin` is an open subscheme of it. -/
@[stacks 04RR]
theorem exists_isOpenImmersion_of_isRepresentable {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ ≫ f = 𝟙 Y)
    {T : Over S} (e : yoneda.obj T ≅ functor f) :
    ∃ (T' : Over S) (ι : T' ⟶ T)
      (e' : yoneda.obj T' ≅ withSectionFunctor f σ hσ),
      AlgebraicGeometry.IsOpenImmersion ι.left ∧
        yoneda.map ι ≫ e.hom = e'.hom ≫ withSectionι f σ hσ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePart
