/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank

/-!
# Duals of finite locally free scheme modules

The internal-Hom dual of a finite locally free module on a scheme is finite locally free.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree

/-- The internal-Hom dual of a finite locally free module on a scheme is finite locally free. -/
noncomputable instance dual {X : Scheme.{u}} (E : X.Modules)
    [E.IsFiniteLocallyFree] : (Scheme.Modules.dual E).IsFiniteLocallyFree := sorry

end AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree
