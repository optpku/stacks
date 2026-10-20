module

public import ReasLib.AlgebraicGeometry.RootsOfUnity.AlgebraicSpace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry CategoryTheory CategoryTheory.MonObj

/- Example 78.7.2 (Roots of unity as a group algebraic space) (1): for a morphism
B ⟶ S as in Section 78.3 and n with NeZero n, the group algebraic space of nth
roots of unity over B is the explicit positive-index product presheaf. -/
@[stacks 043K] #check
  (AlgebraicGeometry.RootsOfUnity.algebraicSpace :
    ∀ (n : ℕ) [NeZero n] {S : AlgebraicGeometry.Scheme} (B : AlgebraicGeometry.AlgebraicSpace S),
      AlgebraicGeometry.AlgebraicSpace S)

/- The structure morphism of the product carrier is the first projection. -/
#check
  (AlgebraicGeometry.RootsOfUnity.algebraicSpace_fst :
    ∀ (n : ℕ) [NeZero n] {S : AlgebraicGeometry.Scheme}
      (B : AlgebraicGeometry.AlgebraicSpace S),
      AlgebraicGeometry.RootsOfUnity.algebraicSpace n B ⟶ B)

/- The product carrier is characterized by its two projections. -/
#check
  (AlgebraicGeometry.RootsOfUnity.algebraicSpaceIsLimit :
    ∀ (n : ℕ) [NeZero n] {S : AlgebraicGeometry.Scheme}
      (B : AlgebraicGeometry.AlgebraicSpace S),
      CategoryTheory.Limits.IsLimit
        (CategoryTheory.Limits.BinaryFan.mk
          (AlgebraicGeometry.RootsOfUnity.algebraicSpace_fst n B)
          (AlgebraicGeometry.RootsOfUnity.algebraicSpace_snd n B)))

/- Example 78.7.2 (Roots of unity as a group algebraic space) (2): the functor sending
a scheme T over B to the subgroup of nth roots of unity in Γ(T.left, ⊤) is
represented by the relative group object, via homMulEquiv. -/
@[stacks 043K] #check
  (AlgebraicGeometry.RootsOfUnity.homMulEquiv :
    ∀ (n : ℕ) [NeZero n] {S : AlgebraicGeometry.Scheme}
      (B : AlgebraicGeometry.AlgebraicSpace S) (T : CategoryTheory.Over S)
      (t : CategoryTheory.yoneda.obj T ⟶ B.functorOfPoints),
      (CategoryTheory.Over.mk t ⟶
        (AlgebraicGeometry.RootsOfUnity.groupSpace n B).X) ≃*
        rootsOfUnity n Γ(T.left, ⊤))

/- The scheme μₙ n over S is RootsOfUnity.baseChange n S, see Example 39.5.2. -/
#check AlgebraicGeometry.RootsOfUnity.baseChange
