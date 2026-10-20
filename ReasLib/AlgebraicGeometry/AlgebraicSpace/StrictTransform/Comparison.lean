/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform

/-!
# Comparison morphisms for strict transforms of algebraic spaces

The strict transform of an algebraic space is a closed subspace of a fibre
product. Its inclusion composed with the two projections supplies the
canonical maps used to iterate strict transforms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical projection from a strict-transform algebraic space to the original
algebraic space. -/
def strictTransformFst {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    (strictTransform b E f).X ⟶ X :=
  (strictTransform b E f).ι ≫ pullback.fst f b

/-- The canonical projection from a strict-transform algebraic space to the
transformed base. -/
def strictTransformSnd {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    (strictTransform b E f).X ⟶ B' :=
  (strictTransform b E f).ι ≫ pullback.snd f b

/-- The first projection is the closed immersion of the strict transform followed by
the first pullback projection. -/
theorem strictTransformFst_eq {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    strictTransformFst b E f = (strictTransform b E f).ι ≫ pullback.fst f b :=
  sorry

/-- The second projection is the closed immersion of the strict transform followed by
the second pullback projection. -/
theorem strictTransformSnd_eq {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    strictTransformSnd b E f = (strictTransform b E f).ι ≫ pullback.snd f b :=
  sorry

/-- The two canonical projections from a strict-transform algebraic space form a
commutative square. -/
theorem strictTransform_condition {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    strictTransformFst b E f ≫ f = strictTransformSnd b E f ≫ b :=
  sorry

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
  rfl

/-- The relative comparison morphism preserves the projection to the original space. -/
theorem strictTransformRelativeMap_fst {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    strictTransformRelativeMap b E f ≫ pullback.fst f b =
      pullback.fst (𝟙 X) (strictTransformFst b E f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
