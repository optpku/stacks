/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.Definition_88_20_1

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigEtale

/-- Lemma 88.20.3: A rig-étale morphism of locally Noetherian formal algebraic
spaces is locally of finite type. -/
@[stacks 0AQN]
instance toLocallyOfFiniteType {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [RigEtale f] : LocallyOfFiniteType f := sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigEtale
