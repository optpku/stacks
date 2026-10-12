/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Fiber

open AlgebraicGeometry

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.Scheme.GeometricPoint.EtaleNeighborhood

variable {S : Scheme.{u}} {s : GeometricPoint S}

/-- The point of a geometric étale neighbourhood lying under its chosen geometric lift. -/
def uniquePoint (U : EtaleNeighborhood s) : U.toEtale.left :=
  U.lift default

/-- The point under the chosen geometric lift maps to the image of the base geometric point. -/
theorem uniquePoint_map (U : EtaleNeighborhood s) :
    U.toEtale.hom (uniquePoint U) = s.image := sorry

/-- A geometric étale neighbourhood determines an ordinary étale neighbourhood of the image
of the base geometric point by selecting the point under its chosen lift. -/
def toPointNeighborhood (U : EtaleNeighborhood s) :
    Scheme.EtaleNeighborhood S s.image :=
  Scheme.EtaleNeighborhood.of U.toEtale (uniquePoint U) (uniquePoint_map U)

/-- The ordinary neighbourhood associated to a geometric neighbourhood has the same étale
scheme, selects the point under the geometric lift, and maps that point to the base image. -/
theorem toPointNeighborhood_spec (U : EtaleNeighborhood s) :
    (toPointNeighborhood U).toEtale = U.toEtale ∧
      (toPointNeighborhood U).point = uniquePoint U ∧
      (toPointNeighborhood U).toEtale.hom (uniquePoint U) = s.image := sorry

/-- Every ordinary étale neighbourhood of the image of a geometric point admits a geometric
étale neighbourhood over that geometric point converting back to the given neighbourhood. -/
theorem exists_ofPointNeighborhood (U : Scheme.EtaleNeighborhood S s.image) :
    ∃ V : EtaleNeighborhood s, toPointNeighborhood V = U := sorry

end AlgebraicGeometry.Scheme.GeometricPoint.EtaleNeighborhood
