/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.EtaleNeighborhood.Correspondence
import StacksCheckRecall

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.GeometricPoint.EtaleNeighborhood

universe u

/- Remark 59.29.3 (1): an étale neighbourhood of a geometric point of `S` determines an
étale neighbourhood of the ordinary point over which it lies, by taking the unique point
of the neighbourhood scheme under the geometric lift. -/
@[stacks 04HT] #check
  (AlgebraicGeometry.Scheme.GeometricPoint.EtaleNeighborhood.toPointNeighborhood_spec :
    ∀ {S : Scheme.{u}} {s : Scheme.GeometricPoint S}
      (U : Scheme.GeometricPoint.EtaleNeighborhood s),
      (toPointNeighborhood U).toEtale = U.toEtale ∧
        (toPointNeighborhood U).point = uniquePoint U ∧
        (toPointNeighborhood U).toEtale.hom (uniquePoint U) = s.image)

/- Remark 59.29.3 (2): given an étale neighbourhood of the ordinary image of a geometric
point, the residue-field extension is finite separable, so there is a geometric étale
neighbourhood of the geometric point on the same underlying étale scheme. -/
@[stacks 04HT] #check
  (AlgebraicGeometry.Scheme.GeometricPoint.EtaleNeighborhood.exists_ofPointNeighborhood :
    ∀ {S : Scheme.{u}} {s : Scheme.GeometricPoint S}
      (U : Scheme.EtaleNeighborhood S s.image),
      ∃ V : Scheme.GeometricPoint.EtaleNeighborhood s, toPointNeighborhood V = U)
