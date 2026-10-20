module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Unibranch
import StacksCheckRecall

/-!
# Unique minimal primes of henselian local rings of decent algebraic spaces

The equivalence and its henselian-local-ring characterizations are owned by
`ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Unibranch`.
-/

universe u

open AlgebraicGeometry AlgebraicSpace TopologicalSpace EtaleNeighborhood

/- Lemma 68.24.1: For a point of a decent algebraic space, unique minimal
primes of all elementary-neighbourhood stalks, unique irreducible components
through their selected points, unibranchness of those stalks, and a unique
minimal prime of the henselian local ring are equivalent. -/
@[stacks 0DQ6]
#check (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing.uniqueMinimalPrime_tfae :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X),
    List.TFAE
      [ ∀ U : Elementary X x,
          ∃! p : Ideal ((scheme U.obj).presheaf.stalk (point U.obj)),
            p ∈ minimalPrimes ((scheme U.obj).presheaf.stalk (point U.obj))
      , ∀ U : Elementary X x,
          ∃! Z, Z ∈ irreducibleComponentsAt (point U.obj)
      , ∀ U : Elementary X x,
          (scheme U.obj).isUnibranchAt (point U.obj)
      , ∃! p : Ideal (henselianLocalRing X x),
          p ∈ minimalPrimes (henselianLocalRing X x) ])

#check (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing.uniqueMinimalPrime_iff_elementaryStalk :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X),
    (∃! p : Ideal (henselianLocalRing X x),
        p ∈ minimalPrimes (henselianLocalRing X x)) ↔
      ∀ U : Elementary X x,
        ∃! p : Ideal ((scheme U.obj).presheaf.stalk (point U.obj)),
          p ∈ minimalPrimes ((scheme U.obj).presheaf.stalk (point U.obj)))

#check (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing.uniqueMinimalPrime_iff_uniqueComponent :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X),
    (∃! p : Ideal (henselianLocalRing X x),
        p ∈ minimalPrimes (henselianLocalRing X x)) ↔
      ∀ U : Elementary X x,
        ∃! Z, Z ∈ irreducibleComponentsAt (point U.obj))

#check (AlgebraicGeometry.AlgebraicSpace.henselianLocalRing.uniqueMinimalPrime_iff_isUnibranchAt_elementary :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X),
    (∃! p : Ideal (henselianLocalRing X x),
        p ∈ minimalPrimes (henselianLocalRing X x)) ↔
      ∀ U : Elementary X x,
        (scheme U.obj).isUnibranchAt (point U.obj))
