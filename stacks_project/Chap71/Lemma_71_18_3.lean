module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap71.Lemma_71_18_3_Comparison
public import stacks_project.Chap71.Lemma_71_18_7_Blowup

/-!
# Strict transform as a blowup, and relative comparison of modules

In the situation of Definition 71.18.1, the strict transform of `X` is the
blowup of `X` in `f⁻¹Z`, and the strict transform of a quasi-coherent module
is the pushforward of its strict transform relative to that induced blowup.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.18.3 (1): in the situation of Definition 71.18.1, the strict transform
of `X` is the blowup of `X` in the closed subspace `f⁻¹Z`. -/
@[stacks 0864]
theorem strictTransformFst_isBlowup {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z] (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b (Z.inverseImage b) f).ι] :
    IsBlowup (strictTransformFst b (Z.inverseImage b) f) (Z.inverseImage f) :=
  sorry

/-- The canonical projection from the strict transform along a blowup carries its
canonical blowup structure. -/
instance instIsBlowup_strictTransformFst {S : Scheme.{u}}
    {B B' X : AlgebraicSpace S} (Z : ClosedSubspace B) (b : B' ⟶ B)
    [IsBlowup b Z] (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b (Z.inverseImage b) f).ι] :
    IsBlowup (strictTransformFst b (Z.inverseImage b) f) (Z.inverseImage f) :=
  strictTransformFst_isBlowup Z b f

/-- Lemma 71.18.3 (2): for a quasi-coherent `𝒪_X`-module `F`, the strict transform
`F'` is canonically isomorphic to the pushforward along `X' ⟶ X ×_B B'` of the
strict transform of `F` relative to the blowing up `X' ⟶ X`. -/
@[stacks 0864]
theorem strictTransformModule_isomorphic_pushforward_relativeStrictTransform
    {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z] (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b (Z.inverseImage b) f).ι]
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIsomorphic
      (strictTransformModule b (Z.inverseImage b) f F)
      ((Modules.pushforward
          (strictTransformRelativeMap b (Z.inverseImage b) f)).obj
        (strictTransformModule
          (strictTransformFst b (Z.inverseImage b) f)
          ((Z.inverseImage f).inverseImage
            (strictTransformFst b (Z.inverseImage b) f))
          (𝟙 X) F)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
