module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranch

/-!
# Unique minimal primes of étale local rings

For an algebraic space, unique minimal primes of stalks of étale scheme neighbourhoods,
unique irreducible components through the selected points, unibranchness and geometric
unibranchness of those local rings, and unique minimal primes of the étale-site stalks
at geometric points over the given point are equivalent.
-/

universe u

open AlgebraicGeometry AlgebraicSpace TopologicalSpace EtaleNeighborhood

/- Lemma 66.23.1: the five criteria for local geometric unibranchness are equivalent. -/
@[stacks 06DK] #check (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing_uniqueMinimalPrime_tfae :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X),
    List.TFAE
      [ ∀ U : EtaleNeighborhood X x,
          ∃! p : Ideal ((scheme U).presheaf.stalk (point U)),
            p ∈ minimalPrimes ((scheme U).presheaf.stalk (point U))
      , ∀ U : EtaleNeighborhood X x,
          ∃! Z, Z ∈ irreducibleComponentsAt (point U)
      , ∀ U : EtaleNeighborhood X x,
          (scheme U).isUnibranchAt (point U)
      , ∀ U : EtaleNeighborhood X x,
          (scheme U).isGeometricallyUnibranchAt (point U)
      , ∀ xbar : GeometricPoint X, xbar.liesOver x →
          ∃! p : Ideal (etaleLocalRing X xbar),
            p ∈ minimalPrimes (etaleLocalRing X xbar) ])

#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing_uniqueMinimalPrime_iff_etaleStalk :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X),
    (∀ xbar : GeometricPoint X, xbar.liesOver x →
        ∃! p : Ideal (etaleLocalRing X xbar),
          p ∈ minimalPrimes (etaleLocalRing X xbar)) ↔
      ∀ U : EtaleNeighborhood X x,
        ∃! p : Ideal ((scheme U).presheaf.stalk (point U)),
          p ∈ minimalPrimes ((scheme U).presheaf.stalk (point U)))

#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing_uniqueMinimalPrime_iff_uniqueComponent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X),
    (∀ xbar : GeometricPoint X, xbar.liesOver x →
        ∃! p : Ideal (etaleLocalRing X xbar),
          p ∈ minimalPrimes (etaleLocalRing X xbar)) ↔
      ∀ U : EtaleNeighborhood X x,
        ∃! Z, Z ∈ irreducibleComponentsAt (point U))

#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing_uniqueMinimalPrime_iff_isUnibranchAt :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X),
    (∀ xbar : GeometricPoint X, xbar.liesOver x →
        ∃! p : Ideal (etaleLocalRing X xbar),
          p ∈ minimalPrimes (etaleLocalRing X xbar)) ↔
      ∀ U : EtaleNeighborhood X x,
        (scheme U).isUnibranchAt (point U))

#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing_uniqueMinimalPrime_iff_isGeometricallyUnibranchAt :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X),
    (∀ xbar : GeometricPoint X, xbar.liesOver x →
        ∃! p : Ideal (etaleLocalRing X xbar),
          p ∈ minimalPrimes (etaleLocalRing X xbar)) ↔
      ∀ U : EtaleNeighborhood X x,
        (scheme U).isGeometricallyUnibranchAt (point U))
