module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Unibranch
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 68.24.2 (1): Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x ∈ |X|`. We say that `X` is unibranch at `x` if the equivalent conditions of
Lemma 68.24.1 hold. -/
@[stacks 0DQ7] #check (AlgebraicGeometry.AlgebraicSpace.isUnibranchAt :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X],
    AlgebraicGeometry.AlgebraicSpace.Points X → Prop)

/- Definition 68.24.2 (2): Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
We say that `X` is unibranch if `X` is unibranch at every `x ∈ |X|`. -/
@[stacks 0DQ7] #check (AlgebraicGeometry.AlgebraicSpace.isUnibranch :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X], Prop)

#check (AlgebraicGeometry.AlgebraicSpace.isUnibranchAt_iff_uniqueMinimalPrime :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
    (x : AlgebraicGeometry.AlgebraicSpace.Points X),
    X.isUnibranchAt x ↔
      ∃! p : Ideal (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing X x),
        p ∈ minimalPrimes (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing X x))
#check (AlgebraicGeometry.AlgebraicSpace.isUnibranch_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X],
    X.isUnibranch ↔ ∀ x : AlgebraicGeometry.AlgebraicSpace.Points X, X.isUnibranchAt x)
