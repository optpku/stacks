module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeneralLinear

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.GeneralLinear
open scoped CategoryTheory.MonObj

universe u

/- Example 78.7.4 (General linear group algebraic space) (1): the group algebraic space
`GLₙ,B` over an algebraic space `B` over a scheme `S` is the fibre product `B ×_S GLₙ,S`,
as the group object `groupSpace B n` in `Over B`. -/
@[stacks 043M] #check
  (AlgebraicGeometry.AlgebraicSpace.GeneralLinear.groupSpace :
    {S : Scheme.{u}} → (B : AlgebraicSpace S) → (n : ℕ) → [NeZero n] →
      AlgebraicGeometry.GroupAlgebraicSpace B)

/- Example 78.7.4 (General linear group algebraic space) (2): morphisms over `B` from a scheme `T`
to `asOver B n` are multiplicatively equivalent to invertible `n × n` matrices
`Matrix.GeneralLinearGroup (ULift (Fin n)) Γ(T.left, ⊤)`. -/
@[stacks 043M] #check
  (AlgebraicGeometry.AlgebraicSpace.GeneralLinear.homOverMulEquiv :
    {S : Scheme.{u}} → {B : AlgebraicSpace S} → (n : ℕ) → [NeZero n] →
      {T : Over S} → (t : AlgebraicGeometry.AlgebraicSpace.ofOver T ⟶ B) →
        (Over.mk t ⟶ AlgebraicGeometry.AlgebraicSpace.GeneralLinear.asOver B n) ≃*
          Matrix.GeneralLinearGroup (ULift.{u} (Fin n)) Γ(T.left, ⊤))

/- Example 78.7.4 (General linear group algebraic space) (3): the represented matrix-valued
functor is natural under precomposition by a morphism of schemes over `S`, with entries pulled
back by the induced map on global sections. The source writes `𝔾ₘ,S` but cites the general-linear
group-scheme example, so the displayed `GLₙ,S` construction is the intended one. -/
@[stacks 043M] #check
  (AlgebraicGeometry.AlgebraicSpace.GeneralLinear.homOverMulEquiv_naturality :
    {S : Scheme.{u}} → {B : AlgebraicSpace S} → (n : ℕ) → [NeZero n] →
      {T T' : Over S} → (g : T' ⟶ T) →
        (t : AlgebraicGeometry.AlgebraicSpace.ofOver T ⟶ B) →
          (h : Over.mk t ⟶ AlgebraicGeometry.AlgebraicSpace.GeneralLinear.asOver B n) →
            AlgebraicGeometry.AlgebraicSpace.GeneralLinear.homOverMulEquiv n
                (AlgebraicGeometry.AlgebraicSpace.GeneralLinear.overMap g ≫ t)
                (AlgebraicGeometry.AlgebraicSpace.GeneralLinear.sliceMap g t ≫ h) =
              Matrix.GeneralLinearGroup.map (Scheme.Γ.map g.left.op).hom
                (AlgebraicGeometry.AlgebraicSpace.GeneralLinear.homOverMulEquiv n t h))
