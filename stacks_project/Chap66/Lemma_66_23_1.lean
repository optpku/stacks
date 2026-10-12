/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.Topology.IrreducibleComponents.AtPoint
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap68.Definition_68_11_5_Neighborhood

/-!
# Unique minimal primes of étale local rings

For an algebraic space, unique minimal primes of stalks of étale scheme neighbourhoods,
unique irreducible components through the selected points, unibranchness and geometric
unibranchness of those local rings, and unique minimal primes of the étale-site stalks
at geometric points over the given point are equivalent.
-/

@[expose] public section

universe u

open AlgebraicGeometry AlgebraicSpace TopologicalSpace EtaleNeighborhood

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Lemma 66.23.1: let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`x` be a point of `|X|`. The following are equivalent: for any étale neighbourhood
`U : EtaleNeighborhood X x` the stalk `(scheme U).presheaf.stalk (point U)` has a unique
minimal prime; for any such neighbourhood there is a unique irreducible component of
`scheme U` through `point U`; for any such neighbourhood `scheme U` is unibranch at
`point U`; for any such neighbourhood `scheme U` is geometrically unibranch at
`point U`; and `etaleLocalRing X xbar` has a unique minimal prime for any geometric
point `xbar` lying over `x`. -/
@[stacks 06DK]
theorem etaleLocalRing_uniqueMinimalPrime_tfae (x : Points X) :
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
            p ∈ minimalPrimes (etaleLocalRing X xbar) ] :=
  sorry

/-- The étale-site stalk at every geometric point over `x` has a unique minimal prime if
and only if every étale neighbourhood of `x` has a unique minimal prime in its local ring
at the selected point. -/
theorem etaleLocalRing_uniqueMinimalPrime_iff_etaleStalk (x : Points X) :
    (∀ xbar : GeometricPoint X, xbar.liesOver x →
        ∃! p : Ideal (etaleLocalRing X xbar),
          p ∈ minimalPrimes (etaleLocalRing X xbar)) ↔
      ∀ U : EtaleNeighborhood X x,
        ∃! p : Ideal ((scheme U).presheaf.stalk (point U)),
          p ∈ minimalPrimes ((scheme U).presheaf.stalk (point U)) :=
  sorry

/-- The étale-site stalk at every geometric point over `x` has a unique minimal prime if
and only if every étale neighbourhood of `x` has a unique irreducible component through
its selected point. -/
theorem etaleLocalRing_uniqueMinimalPrime_iff_uniqueComponent (x : Points X) :
    (∀ xbar : GeometricPoint X, xbar.liesOver x →
        ∃! p : Ideal (etaleLocalRing X xbar),
          p ∈ minimalPrimes (etaleLocalRing X xbar)) ↔
      ∀ U : EtaleNeighborhood X x,
        ∃! Z, Z ∈ irreducibleComponentsAt (point U) :=
  sorry

/-- The étale-site stalk at every geometric point over `x` has a unique minimal prime if
and only if every étale neighbourhood of `x` is unibranch at its selected point. -/
theorem etaleLocalRing_uniqueMinimalPrime_iff_isUnibranchAt (x : Points X) :
    (∀ xbar : GeometricPoint X, xbar.liesOver x →
        ∃! p : Ideal (etaleLocalRing X xbar),
          p ∈ minimalPrimes (etaleLocalRing X xbar)) ↔
      ∀ U : EtaleNeighborhood X x,
        (scheme U).isUnibranchAt (point U) :=
  sorry

/-- The étale-site stalk at every geometric point over `x` has a unique minimal prime if
and only if every étale neighbourhood of `x` is geometrically unibranch at its selected
point. -/
theorem etaleLocalRing_uniqueMinimalPrime_iff_isGeometricallyUnibranchAt (x : Points X) :
    (∀ xbar : GeometricPoint X, xbar.liesOver x →
        ∃! p : Ideal (etaleLocalRing X xbar),
          p ∈ minimalPrimes (etaleLocalRing X xbar)) ↔
      ∀ U : EtaleNeighborhood X x,
        (scheme U).isGeometricallyUnibranchAt (point U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
