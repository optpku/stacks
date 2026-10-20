/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.K0.Support.Ring
import StacksCheckRecall

open CategoryTheory

universe u

variable {X Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
  [AlgebraicGeometry.IsClosedImmersion i]

/- Remark 36.38.9 (1): the perfect derived `𝒪_X`-modules whose cohomology is
set-theoretically supported on the closed subscheme `Z` form a full subcategory. -/
@[stacks 0FDN] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base) :
    Type (u + 1))

/- Remark 36.38.9 (2): this supported-perfect object property is strictly full. -/
@[stacks 0FDN] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.perfectSupportedOn_isClosedUnderIsomorphisms
    (Set.range i.base) :
      (AlgebraicGeometry.RingedSpace.ModuleDerived.perfectSupportedOn
        (Set.range i.base)).IsClosedUnderIsomorphisms)

/- Remark 36.38.9 (3): the supported-perfect subcategory is triangulated. -/
@[stacks 0FDN] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.perfectSupportedOn_isTriangulated
    (Set.range i.base) :
      (AlgebraicGeometry.RingedSpace.ModuleDerived.perfectSupportedOn
        (Set.range i.base)).IsTriangulated)

/- Remark 36.38.9 (4): the supported-perfect subcategory is saturated under retracts. -/
@[stacks 0FDN] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.perfectSupportedOn_isStableUnderRetracts
    (Set.range i.base) :
      (AlgebraicGeometry.RingedSpace.ModuleDerived.perfectSupportedOn
        (Set.range i.base)).IsStableUnderRetracts)

/- Remark 36.38.9 (5): its zeroth triangulated Grothendieck group is
`K0WithSupport X (Set.range i.base)`. -/
@[stacks 0FDN] #check
  (AlgebraicGeometry.Scheme.K0WithSupport X (Set.range i.base) : Type (u + 1))

/- Remark 36.38.9 (6): multiplication of generator classes is induced by derived tensor
product. -/
@[stacks 0FDN] #check
  (AlgebraicGeometry.Scheme.K0WithSupport.mul_of X (Set.range i.base) :
    ∀ (K L : AlgebraicGeometry.RingedSpace.ModuleDerived.PerfectSupportedOn
        (Set.range i.base)),
      AlgebraicGeometry.Scheme.K0WithSupport.mul X (Set.range i.base)
          (CategoryTheory.TriangulatedK0.of K) (CategoryTheory.TriangulatedK0.of L) =
        CategoryTheory.TriangulatedK0.of
          (AlgebraicGeometry.Scheme.K0WithSupport.tensorObj X (Set.range i.base) K L))

/- Remark 36.38.9 (7): supported perfect `K₀` has a canonical associative and commutative
multiplication, expressed by `NonUnitalCommRing`; no unit is required in general. -/
@[stacks 0FDN] #check
  (AlgebraicGeometry.Scheme.K0WithSupport.instNonUnitalCommRing X (Set.range i.base) :
    NonUnitalCommRing
      (AlgebraicGeometry.Scheme.K0WithSupport X (Set.range i.base)))
