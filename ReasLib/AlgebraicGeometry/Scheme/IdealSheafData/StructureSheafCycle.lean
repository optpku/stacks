/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Union
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Finite

/-!
# Cycles of structure sheaves of closed subschemes

This file identifies the support of the pushed-forward structure sheaf of a closed subscheme
and compares its associated cycle with the cycle of the closed subscheme.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The ambient support of the pushed-forward structure sheaf of a closed subscheme is its
underlying closed subset. -/
theorem closedSubschemeStructureSheafOn_support (Z : X.IdealSheafData) :
    RingedSpace.moduleSupport (closedSubschemeStructureSheafOn Z) = (Z.support : Set X) := sorry

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- If a closed subscheme has relative dimension at most `k`, then its degree-`k` cycle equals
the degree-`k` cycle associated to its pushed-forward structure sheaf. -/
theorem cycle_eq_associatedCycle
    {S X : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (Z : X.IdealSheafData) (k : ℤ)
    (hZ : f.closedSubschemeDeltaDimension δ Z ≤ (k : EInt)) :
    -- Local instance justification (proof-local temporary data): `f` canonically supplies `IsLocallyNoetherian X`, but it is not inferable from `X` alone.
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (f.closedSubschemeCycle δ Z k hZ : AlgebraicCycle X ℤ) =
      (closedSubschemeStructureSheafOn Z).associatedCycle
        (f.relativeDimensionFunction δ) k := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
