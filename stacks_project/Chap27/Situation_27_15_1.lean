/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Quasicoherent

@[expose] public section

universe u

variable (S : AlgebraicGeometry.Scheme.{u})

/- Situation 27.15.1: here `S` is a scheme, and `𝒜` is a quasi-coherent graded `𝒪_S`-algebra. -/
@[stacks 01NN] #check
  (SheafOfModules.RingedSite.GradedAlgebraSheaf.IsQuasicoherent.{u, u} :
    SheafOfModules.RingedSite.GradedAlgebraSheaf.{u, u} S.sheaf ℤ → Prop)
