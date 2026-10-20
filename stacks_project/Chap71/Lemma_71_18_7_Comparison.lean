module

public import stacks_project.Chap71.Definition_71_18_1_StrictTransform
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.Comparison

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

#check (AlgebraicGeometry.AlgebraicSpace.strictTransformFst :
    ∀ {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι],
    (strictTransform b E f).X ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.strictTransformSnd :
    ∀ {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι],
    (strictTransform b E f).X ⟶ B')

#check (AlgebraicGeometry.AlgebraicSpace.strictTransformFst_eq :
    ∀ {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι],
    strictTransformFst b E f = (strictTransform b E f).ι ≫ pullback.fst f b)

#check (AlgebraicGeometry.AlgebraicSpace.strictTransformSnd_eq :
    ∀ {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι],
    strictTransformSnd b E f = (strictTransform b E f).ι ≫ pullback.snd f b)

#check (AlgebraicGeometry.AlgebraicSpace.strictTransform_condition :
    ∀ {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
    (b : B' ⟶ B) (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι],
    strictTransformFst b E f ≫ f = strictTransformSnd b E f ≫ b)

end AlgebraicGeometry.AlgebraicSpace
