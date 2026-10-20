module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.Blowup
import StacksCheckRecall

/-!
# Strict transform as a blowup, and relative comparison of modules

In the situation of Definition 71.18.1, the strict transform of `X` is the
blowup of `X` in `f⁻¹Z`, and the strict transform of a quasi-coherent module
is canonically the pushforward of its strict transform relative to that blowup.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 71.18.3 (1): the strict transform of `X` is the blowup in `f⁻¹Z`. -/
@[stacks 0864] #check
  (AlgebraicGeometry.AlgebraicSpace.strictTransformFst_isBlowup :
    ∀ {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
      (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z] (f : X ⟶ B)
      [QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι],
      IsBlowup (strictTransformFst b (Z.inverseImageSubspace b) f)
        (Z.inverseImageSubspace f))

/- Lemma 71.18.3 (2): the strict transform of a quasi-coherent module is canonically
isomorphic to the pushforward of its strict transform relative to `X' ⟶ X`. -/
@[stacks 0864] #check
  (AlgebraicGeometry.AlgebraicSpace.strictTransformModule_isomorphic_pushforward_relativeStrictTransform :
    ∀ {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
      (Z : ClosedSubspace B) (b : B' ⟶ B) [IsBlowup b Z] (f : X ⟶ B)
      [QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι]
      (F : X.Modules) [F.IsQuasicoherent],
      ∃ e : strictTransformModule b (Z.inverseImageSubspace b) f F ≅
        (Modules.pushforward
          (strictTransformRelativeMap b (Z.inverseImageSubspace b) f)).obj
          (strictTransformModule
            (strictTransformFst b (Z.inverseImageSubspace b) f)
            ((Z.inverseImageSubspace f).inverseImageSubspace
              (strictTransformFst b (Z.inverseImageSubspace b) f))
            (𝟙 X) F),
        strictTransformπ b (Z.inverseImageSubspace b) f F ≫ e.hom =
          strictTransformRelativeπ Z b f F)
