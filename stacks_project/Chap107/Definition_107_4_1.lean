module

public import stacks_project.Chap107.Definition_107_4_1_FormalBranches
public import stacks_project.Chap107.Definition_107_4_1_VersalRing

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Definition 107.4.1: Let `X` be an algebraic stack locally of finite type
over a locally Noetherian scheme `S`. Let `x0 : Spec(k) ⟶ X` be a morphism
where `k` is a field of finite type over `S`. The formal branches of `X`
through `x0` is the set of irreducible components of `Spec(A)` for any
choice of versal ring to `X` at `x0`, identified for different choices of
`A` by the formally smooth power-series comparison of minimal primes. -/
@[stacks 0DRA]
abbrev formalBranches {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyOfFiniteType X]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom] :
    Type (u + 1) :=
  FormalBranches x0

/-- For any versal formal object `ξ` of `X` at `x0`, every formal branch arises
uniquely from an irreducible component of `Spec(ξ.base)`. -/
theorem formalBranches_spec {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyOfFiniteType X]
    (x0 : FieldValuedPoint X) [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (ξ : GroupoidsOver.FormalObject X)
    [GroupoidsOver.FormalObject.IsVersal ξ] (hξ : StageOneCompatible x0 ξ) :
    Function.Surjective (FormalBranches.mk x0 ξ hξ) ∧
      ∀ Z W, FormalBranches.mk x0 ξ hξ Z = FormalBranches.mk x0 ξ hξ W ↔
        Z = W := sorry

end AlgebraicGeometry.AlgebraicStack

