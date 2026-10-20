module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.Topology.IrreducibleComponents.AtPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Defs

/-!
# Unique minimal primes of henselian local rings of decent algebraic spaces

On a decent algebraic space, unique minimal primes of stalks of elementary étale
neighbourhoods, unique irreducible components through the selected points,
unibranchness of those local rings, and unique minimal primes of the henselian
local ring are equivalent.
-/

@[expose] public section

universe u

open AlgebraicGeometry AlgebraicSpace TopologicalSpace EtaleNeighborhood

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] (x : Points X)

/-- Let `S` be a scheme. Let `X` be a decent algebraic space over `S`.
Let `x : Points X`. The following are equivalent: for any elementary étale
neighbourhood `U : Elementary X x` the stalk
`(scheme U.obj).presheaf.stalk (point U.obj)` has a unique minimal prime; for any
such neighbourhood there is a unique irreducible component of `U` through
`point U.obj`; for any such neighbourhood `scheme U.obj` is unibranch at
`point U.obj`; and `henselianLocalRing X x` has a unique minimal prime. -/
@[stacks 0DQ6]
theorem henselianLocalRing.uniqueMinimalPrime_tfae :
    List.TFAE
      [ ∀ U : Elementary X x,
          ∃! p : Ideal ((scheme U.obj).presheaf.stalk (point U.obj)),
            p ∈ minimalPrimes ((scheme U.obj).presheaf.stalk (point U.obj))
      , ∀ U : Elementary X x,
          ∃! Z, Z ∈ irreducibleComponentsAt (point U.obj)
      , ∀ U : Elementary X x,
          (scheme U.obj).isUnibranchAt (point U.obj)
      , ∃! p : Ideal (henselianLocalRing X x),
          p ∈ minimalPrimes (henselianLocalRing X x) ] :=
  sorry

/-- The henselian local ring of a decent algebraic space at a point has a unique
minimal prime if and only if every elementary étale neighbourhood has a unique
minimal prime in its local ring at the selected point. -/
theorem henselianLocalRing.uniqueMinimalPrime_iff_elementaryStalk :
    (∃! p : Ideal (henselianLocalRing X x),
        p ∈ minimalPrimes (henselianLocalRing X x)) ↔
      ∀ U : Elementary X x,
        ∃! p : Ideal ((scheme U.obj).presheaf.stalk (point U.obj)),
          p ∈ minimalPrimes ((scheme U.obj).presheaf.stalk (point U.obj)) :=
  sorry

/-- The henselian local ring of a decent algebraic space at a point has a unique
minimal prime if and only if every elementary étale neighbourhood has a unique
irreducible component through its selected point. -/
theorem henselianLocalRing.uniqueMinimalPrime_iff_uniqueComponent :
    (∃! p : Ideal (henselianLocalRing X x),
        p ∈ minimalPrimes (henselianLocalRing X x)) ↔
      ∀ U : Elementary X x,
        ∃! Z, Z ∈ irreducibleComponentsAt (point U.obj) :=
  sorry

/-- The henselian local ring of a decent algebraic space at a point has a unique
minimal prime if and only if every elementary étale neighbourhood is unibranch
at its selected point. -/
theorem henselianLocalRing.uniqueMinimalPrime_iff_isUnibranchAt_elementary :
    (∃! p : Ideal (henselianLocalRing X x),
        p ∈ minimalPrimes (henselianLocalRing X x)) ↔
      ∀ U : Elementary X x,
        (scheme U.obj).isUnibranchAt (point U.obj) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
