module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap71.Lemma_71_18_7_Blowup
public import stacks_project.Chap71.Lemma_71_18_7_Comparison

/-!
# Composition of successive blowups and strict transforms

If two successive blowups of algebraic spaces compose to the blowup in a closed
subspace whose underlying point-set is the union of the first center and the
image of the second, then direct strict transforms agree with iterated strict
transforms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.18.7 (1): if two successive blowups of algebraic spaces compose to the
blowup in a center whose support is the union of the first center and the image of
the second, then the direct strict transform of a quasicoherent module is isomorphic
to its iterated strict transform after the canonical pullback-pasting transport. -/
@[stacks 0868]
theorem strictTransformModule_isomorphic_pushforward_iteratedStrictTransform
    {S : Scheme.{u}} {B B' B'' X : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z]
    (Z' : ClosedSubspace B') (b' : B'' ⟶ B') [IsBlowup b' Z']
    (Y : ClosedSubspace B)
    (hY : Y.pointsSet = Z.pointsSet ∪ Points.map b '' Z'.pointsSet)
    [IsBlowup (b' ≫ b) Y]
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent] :
    IsIsomorphic
      (strictTransformModule (b' ≫ b) (Y.inverseImage (b' ≫ b)) f F)
      ((Modules.pushforward (pullbackLeftPullbackSndIso f b b').hom).obj
        (strictTransformModule b' (Z'.inverseImage b') (pullback.snd f b)
          (strictTransformModule b (Z.inverseImage b) f F))) :=
  sorry

/-- Lemma 71.18.7 (2): under the same hypotheses, the direct strict transform of an
algebraic space is isomorphic to its iterated strict transform formed using the
canonical structure morphism of the first strict transform. -/
@[stacks 0868]
theorem strictTransform_isomorphic_iteratedStrictTransform
    {S : Scheme.{u}} {B B' B'' X : AlgebraicSpace S}
    (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z]
    (Z' : ClosedSubspace B') (b' : B'' ⟶ B') [IsBlowup b' Z']
    (Y : ClosedSubspace B)
    (hY : Y.pointsSet = Z.pointsSet ∪ Points.map b '' Z'.pointsSet)
    [IsBlowup (b' ≫ b) Y]
    (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b (Z.inverseImage b) f).ι]
    [QuasiCompact
      (strictTransformOpenComplement b' (Z'.inverseImage b')
        (strictTransformSnd b (Z.inverseImage b) f)).ι]
    [QuasiCompact
      (strictTransformOpenComplement (b' ≫ b) (Y.inverseImage (b' ≫ b)) f).ι] :
    IsIsomorphic
      (strictTransform (b' ≫ b) (Y.inverseImage (b' ≫ b)) f).X
      (strictTransform b' (Z'.inverseImage b')
        (strictTransformSnd b (Z.inverseImage b) f)).X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
