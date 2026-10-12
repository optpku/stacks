/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Definition_71_18_1_StrictTransform
public import stacks_project.Chap71.Lemma_71_18_7_Comparison

/-!
# Relative comparison morphism for strict transforms

The commutative square of a strict transform induces a canonical morphism from
the relative fibre product `X ×_X X'` to the original ambient `X ×_B B'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical map from the relative strict-transform ambient algebraic space to
the original strict-transform ambient algebraic space. -/
def strictTransformRelativeMap {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    strictTransformAmbient (strictTransformFst b E f) (𝟙 X) ⟶
      strictTransformAmbient b f :=
  pullback.map (𝟙 X) (strictTransformFst b E f) f b
    (𝟙 X) (strictTransformSnd b E f) f rfl (strictTransform_condition b E f)

/-- The relative comparison morphism is the pullback map of the identity on `X`
and the two canonical projections of the strict transform. -/
theorem strictTransformRelativeMap_eq {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    strictTransformRelativeMap b E f =
      pullback.map (𝟙 X) (strictTransformFst b E f) f b
        (𝟙 X) (strictTransformSnd b E f) f rfl
        (strictTransform_condition b E f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
