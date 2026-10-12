/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure.Finiteness
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.StructureSheafCycle

/-!
# Structure sheaves of reduced point closures

This file records coherence and support bounds for the structure sheaf of a reduced point
closure, viewed as a module on the ambient scheme.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PointClosure

/-- The pushed-forward structure sheaf of a reduced point closure in a locally Noetherian
scheme is coherent. -/
instance instIsCoherentStructureSheafOn {X : Scheme.{u}} [IsLocallyNoetherian X] (x : X) :
    (closedSubschemeStructureSheafOn (reducedStructure x).ideal).IsCoherent := sorry

/-- The pushed-forward structure sheaf of the reduced closure of a point of relative
dimension `k` is supported in relative dimension at most `k`. -/
theorem structureSheafOn_support_le
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ) (x : X)
    (hx : f.relativeDimensionFunction δ x = k) :
    ∀ y ∈ RingedSpace.moduleSupport
      (closedSubschemeStructureSheafOn (reducedStructure x).ideal),
      f.relativeDimensionFunction δ y ≤ k := sorry

end AlgebraicGeometry.Scheme.PointClosure
