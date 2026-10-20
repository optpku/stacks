module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Noetherian
import StacksCheckRecall

/-!
# Locally of finite type over locally Noetherian algebraic spaces

A morphism of algebraic spaces that is locally of finite type into a
locally Noetherian target has locally Noetherian source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.23.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is locally of finite type and `Y` is
locally Noetherian, then `X` is locally Noetherian. -/
@[stacks 04ZK] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.isLocallyNoetherian :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f]
      [AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian Y],
      AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian X)
