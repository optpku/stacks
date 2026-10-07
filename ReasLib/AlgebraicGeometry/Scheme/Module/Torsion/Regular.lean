module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Regular

/-!
# Torsion-free modules on low-dimensional regular schemes
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module on an integral regular scheme of topological Krull dimension at most one
is torsion free if and only if it is finite locally free. -/
@[stacks 0CC4]
theorem isTorsionFree_iff_isFiniteLocallyFree_of_topologicalKrullDim_le_one
    {X : Scheme.{u}} [IsIntegral X] [Scheme.Regular X]
    (ℱ : X.Modules) [ℱ.IsCoherent] (hdim : topologicalKrullDim X ≤ 1) :
    IsTorsionFree ℱ ↔ SheafOfModules.IsFiniteLocallyFree ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
