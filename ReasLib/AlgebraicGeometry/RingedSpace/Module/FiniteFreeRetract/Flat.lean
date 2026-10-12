/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FiniteFreeRetract
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat

/-!
# Flat finitely presented module sheaves on ringed spaces

This leaf exposes the point-neighborhood form of the generic ringed-site finite-free-retract
criterion without leaking slice-site implementation instances into geometric statements.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules

variable {X : RingedSpace.{u}}

/-- Lemma 17.18.3 (08BL): a flat finitely presented module sheaf is a retract of a finite free
module sheaf on a neighborhood of every point. -/
@[stacks 08BL]
theorem existsNeighborhoodRetract (M : X.Modules)
    [M.IsFinitePresentation] [M.IsFlat] (x : X) :
    ∃ (U : Opens X) (_ : x ∈ U) (I : Type u), Finite I ∧
      Nonempty (Retract (M.over U) (SheafOfModules.free.{u} I)) := sorry

end AlgebraicGeometry.RingedSpace.Modules
