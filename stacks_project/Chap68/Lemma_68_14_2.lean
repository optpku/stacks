module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent.Singleton
import StacksCheckRecall

/-!
# Decent algebraic spaces with a singleton underlying space

A decent algebraic space whose space of points is a singleton is a scheme. If it
is moreover reduced, it is isomorphic over the base to the spectrum of a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.14.2 (1): If `X` is a decent algebraic space over a scheme `S` and
`Points X` is a singleton, then `X` is a scheme. -/
@[stacks 047Z] #check
  (AlgebraicGeometry.AlgebraicSpace.IsScheme.of_singleton_points :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsDecent X] [Nonempty (Points X)] [Subsingleton (Points X)],
      IsScheme X)

/- Lemma 68.14.2 (2): If `X` is a reduced decent algebraic space over a scheme `S`
and `Points X` is a singleton, then there exist a field `k` and a morphism
`σ : Spec (.of k) ⟶ S` such that `X` is isomorphic over `S` to
`ofOver (Over.mk σ)`. -/
@[stacks 047Z] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_iso_spec_of_singleton :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
      [IsDecent X] [IsReduced X] [Nonempty (Points X)] [Subsingleton (Points X)],
      ∃ (k : Type u) (_ : Field k) (σ : Spec (.of k) ⟶ S),
        Nonempty (X ≅ ofOver (Over.mk σ)))
