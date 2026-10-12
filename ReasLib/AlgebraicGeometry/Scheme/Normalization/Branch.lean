/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Instances.ENat
public import ReasLib.AlgebraicGeometry.Scheme.Branch
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Coproduct.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PointsOver

/-!
# Branch numbers through normalization fibers

This leaf relates branch counts at a scheme point to the point fiber of its
generic-point normalization.  The general point-fiber and residue-field API
is owned by `Scheme.Hom.PointsOver`.
-/

@[expose] public section

open AlgebraicGeometry
open scoped BigOperators

universe u v

noncomputable section

namespace AlgebraicGeometry.Scheme.Normalization

variable {X : Scheme.{u}} [HasFiniteIrreducibleComponentsOnCompactOpens X]

/-- The branch number at a scheme point is the extended cardinality of the
point fiber of the normalization over that point. -/
@[stacks 0C1S]
theorem branchNumberAt_eq_fiberCard
    (x : X) (Ah : Type v) [CommRing Ah] [Algebra (X.presheaf.stalk x) Ah]
    [IsHenselizationOf (X.presheaf.stalk x) Ah] :
    X.branchNumberAt x Ah =
      (Set.univ : Set (X.normalizationTo.pointsOver x)).encard := sorry

/-- The geometric branch number at a scheme point is the sum, over its
normalization fiber, of the separable degrees of the residue fields over the
residue field at that point. -/
@[stacks 0C1S]
theorem geometricBranchNumberAt_eq_tsumSepDegree
    (x : X) (Ash : Type v) [CommRing Ash] [Algebra (X.presheaf.stalk x) Ash]
    [IsStrictHenselizationOf (X.presheaf.stalk x) Ash] :
    X.geometricBranchNumberAt x Ash =
      ∑' xnu : X.normalizationTo.pointsOver x,
        (Field.finSepDegree (X.residueField x)
          ((X.normalization).residueField xnu) : ℕ∞) := sorry

end AlgebraicGeometry.Scheme.Normalization
