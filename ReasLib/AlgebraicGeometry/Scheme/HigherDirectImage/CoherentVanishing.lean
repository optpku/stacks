/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent

/-!
# Coherent vanishing above fibre dimension

For a proper morphism to a locally Noetherian scheme, the stalk of a higher direct image
of a coherent module vanishes above the dimension of the scheme-theoretic fibre.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The stalk of a coherent higher direct image vanishes above the dimension of the fibre. -/
@[stacks 02V7]
theorem higherDirectImageModule_stalk_isZero_of_proper_fiberDimension
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f]
    (y : Y) (d : WithBot ℕ∞)
    (hdim : topologicalKrullDim (f.fiber y) = d)
    (F : X.Modules) [F.IsCoherent] (p : ℕ) (hp : d < (p : WithBot ℕ∞)) :
    IsZero (RingedSpace.stalkModuleCat
      (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y) := sorry

end AlgebraicGeometry.Scheme
