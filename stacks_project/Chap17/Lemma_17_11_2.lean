/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable {X : RingedSpace.{u}}
variable (G : RingedSpace.Modules X) [G.IsFinitePresentation]

/- Lemma 17.11.2 (01BO): any `𝒪_X`-module of finite presentation on a ringed space
`(X, 𝒪_X)` is quasi-coherent. This is the canonical instance from
`SheafOfModules.IsFinitePresentation` to `SheafOfModules.IsQuasicoherent`. -/
@[stacks 01BO]
#check (inferInstance : G.IsQuasicoherent)
