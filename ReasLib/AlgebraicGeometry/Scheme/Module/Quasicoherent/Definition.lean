/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

universe u

@[expose] public section

open AlgebraicGeometry

namespace SheafOfModules

/-- A scheme module is quasi-coherent when its underlying sheaf of modules is quasi-coherent. -/
def isQuasicoherentModule {X : Scheme.{u}} (F : X.Modules) : Prop := F.IsQuasicoherent

end SheafOfModules
