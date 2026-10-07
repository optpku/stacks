module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_21_2_QuasiAffine
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite

/-!
# Neighbourhood schemes for separated locally quasi-finite morphisms

The image of a quasi-affine open in an étale base change of a separated,
locally quasi-finite morphism of algebraic spaces is a quasi-compact open
subspace which is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.50.1: Let `S` be a scheme. Given a commutative diagram of algebraic
spaces over `S` whose inner square is a fibre product `T' ×_T X`, if `T' ⟶ T`
is an étale morphism of affine schemes, `X ⟶ T` is separated and locally
quasi-finite, `V'` is an open subspace of `T' ×_T X`, and `V' ⟶ T'` is
quasi-affine, then the image `U` of `V'` in `X` is a quasi-compact open
subspace of `X` which is representable. -/
@[stacks 03XW]
theorem exists_quasiCompact_scheme_image {S : Scheme.{u}}
    {T T' X P : AlgebraicSpace S} {h : T' ⟶ T} {f : X ⟶ T}
    {pT' : P ⟶ T'} {pX : P ⟶ X} (V' : OpenSubspace P)
    [IsAffine T] [IsAffine T'] [Etale h] [Separated f]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (hpb : IsPullback pT' pX h f) [QuasiAffine (V'.ι ≫ pT')] :
    ∃ U : OpenSubspace X,
      U.pointsSet = Set.range (Points.map (V'.ι ≫ pX)) ∧
        IsQuasiCompact U.X ∧ IsScheme U.X :=
  sorry

/-- The image of `|V'|` in `|X|` is open. -/
theorem isOpen_imagePoints {S : Scheme.{u}}
    {T T' X P : AlgebraicSpace S} {h : T' ⟶ T} {f : X ⟶ T}
    {pT' : P ⟶ T'} {pX : P ⟶ X} (V' : OpenSubspace P)
    [IsAffine T] [IsAffine T'] [Etale h] [Separated f]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (hpb : IsPullback pT' pX h f) [QuasiAffine (V'.ι ≫ pT')] :
    IsOpen (Set.range (Points.map (V'.ι ≫ pX))) :=
  sorry

/-- An open subspace of `X` occupying the image of `|V'|` is quasi-compact. -/
theorem isQuasiCompact_imageOpen {S : Scheme.{u}}
    {T T' X P : AlgebraicSpace S} {h : T' ⟶ T} {f : X ⟶ T}
    {pT' : P ⟶ T'} {pX : P ⟶ X} (V' : OpenSubspace P)
    [IsAffine T] [IsAffine T'] [Etale h] [Separated f]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (hpb : IsPullback pT' pX h f) [QuasiAffine (V'.ι ≫ pT')]
    (U : OpenSubspace X)
    (hU : U.pointsSet = Set.range (Points.map (V'.ι ≫ pX))) :
    IsQuasiCompact U.X :=
  sorry

/-- An open subspace of `X` occupying the image of `|V'|` is representable. -/
theorem isScheme_imageOpen {S : Scheme.{u}}
    {T T' X P : AlgebraicSpace S} {h : T' ⟶ T} {f : X ⟶ T}
    {pT' : P ⟶ T'} {pX : P ⟶ X} (V' : OpenSubspace P)
    [IsAffine T] [IsAffine T'] [Etale h] [Separated f]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (hpb : IsPullback pT' pX h f) [QuasiAffine (V'.ι ≫ pT')]
    (U : OpenSubspace X)
    (hU : U.pointsSet = Set.range (Points.map (V'.ι ≫ pX))) :
    IsScheme U.X :=
  sorry

/-- Chosen-pullback form, with `T' ×_T X` as `pullback h f`. -/
theorem exists_quasiCompact_scheme_image_pullback {S : Scheme.{u}}
    {T T' X : AlgebraicSpace S} {h : T' ⟶ T} {f : X ⟶ T}
    (V' : OpenSubspace (pullback h f))
    [IsAffine T] [IsAffine T'] [Etale h] [Separated f]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [QuasiAffine (V'.ι ≫ pullback.fst h f)] :
    ∃ U : OpenSubspace X,
      U.pointsSet = Set.range (Points.map (V'.ι ≫ pullback.snd h f)) ∧
        IsQuasiCompact U.X ∧ IsScheme U.X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
