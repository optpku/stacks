/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap82.Remark_82_5_1_IrreducibleComponent

/-!
# Irreducible components of a closed subspace in the good setup

In Situation 82.2.1, for good `X / B` and a closed subspace `Y ⊂ X`, irreducible
components of `|Y|` correspond to generic points of those components and to
integral closed subspaces `Z ⊂ Y` with `|Z|` a component of `|Y|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Remark 82.5.1 (1): in Situation 82.2.1, if `X / B` is good and `Y ⊂ X` is a
closed subspace, then irreducible components `T` of `|Y|` are in 1-to-1
correspondence with generic points of those components. The generic point of `T`
is the unique `ξ ∈ genericPoints Y.X` with `closure {ξ} = T`. This chapter calls
`ξ ∈ |Z|` the generic point of an irreducible component `Z` of `Y`. -/
@[stacks 0EE8]
theorem irreducibleComponents_equiv_genericPoints {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (Y : ClosedSubspace X)
    (T : irreducibleComponents (Points Y.X)) :
    ∃! ξ : Points Y.X,
      ξ ∈ genericPoints Y.X ∧
        closure ({ξ} : Set (Points Y.X)) = (T : Set (Points Y.X)) :=
  sorry

/-- Remark 82.5.1 (2): in Situation 82.2.1, if `X / B` is good and `Y ⊂ X` is a
closed subspace, then each irreducible component `T` of `|Y|` is the point-set of
a unique integral closed subspace `Z ⊂ Y`. Uniqueness is a unique morphism over
`Y`. This chapter calls such a `Z` an irreducible component of `Y`. -/
@[stacks 0EE8]
theorem existsUnique_irreducibleComponent {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [IsQuasiSeparated B] (f : X ⟶ B)
    [QuasiSeparated f] [LocallyOfFiniteType f] (Y : ClosedSubspace X)
    (T : irreducibleComponents (Points Y.X)) :
    ∃ Z : ClosedSubspace Y.X,
      IsIntegral Z.X ∧
        Z.pointsSet = (T : Set (Points Y.X)) ∧
          ∀ (Z' : ClosedSubspace Y.X),
            IsIntegral Z'.X →
              Z'.pointsSet = (T : Set (Points Y.X)) →
                ∃! g : Z'.X ⟶ Z.X, g ≫ Z.ι = Z'.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
