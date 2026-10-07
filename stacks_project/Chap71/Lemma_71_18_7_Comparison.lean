module

public import stacks_project.Chap71.Definition_71_18_1_StrictTransform

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

end AlgebraicGeometry.AlgebraicSpace
