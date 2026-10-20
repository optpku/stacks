module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap99.«99_7_1_2_Functor»
public import stacks_project.Chap99.Lemma_99_7_8_Pushout

/-!
# Lemma 99.7.8

In Situation 99.7.1, a pushout square of schemes over `B` whose vertical arrow
is a thickening and whose horizontal arrow is affine induces a bijective
restriction map on `functor f F` and, if `X ⟶ B` is locally of finite
presentation, on `fpFunctor f F`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

/-- Lemma 99.7.8 (1): in Situation 99.7.1, for a pushout square of schemes over
`B` where `Z ⟶ Z'` is a thickening and `Z ⟶ Y` is affine, the natural map
`pushoutComparison (functor f F) H.w` is bijective. -/
@[stacks 08IW]
theorem pushoutComparison_bijective {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {Z Z' Y Y' : SchemesOver B} (i : Z ⟶ Z') (g : Z ⟶ Y)
    (inl : Z' ⟶ Y') (inr : Y ⟶ Y')
    [IsThickening i.left.left] [IsAffineHom g.left.left]
    (H : IsPushout i g inl inr) :
    Function.Bijective (pushoutComparison (functor f F) H.w) :=
  sorry

/-- Lemma 99.7.8 (2): in Situation 99.7.1, if `X ⟶ B` is locally of finite
presentation, then the same comparison is bijective for `fpFunctor f F`. -/
@[stacks 08IW]
theorem fpPushoutComparison_bijective {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [LocallyOfFinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] {Z Z' Y Y' : SchemesOver B} (i : Z ⟶ Z') (g : Z ⟶ Y)
    (inl : Z' ⟶ Y') (inr : Y ⟶ Y')
    [IsThickening i.left.left] [IsAffineHom g.left.left]
    (H : IsPushout i g inl inr) :
    Function.Bijective (pushoutComparison (fpFunctor f F) H.w) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
