module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth
import Mathlib.Tactic.CrossRefAttribute

/-!
# Differentials of formally smooth scheme morphisms

The sheaf of relative differentials of a formally smooth scheme morphism is locally projective.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormallySmooth

/-- The sheaf of relative differentials of a formally smooth scheme morphism is locally
projective. -/
@[stacks 06B5]
instance instIsLocallyProjectiveRelativeDifferentials
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FormallySmooth f] :
    Scheme.Modules.IsLocallyProjective Ω[f.toShHom] := sorry

end AlgebraicGeometry.FormallySmooth
