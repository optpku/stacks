/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Quasi-coherent module sheaves on schemes
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A scheme module is quasi-coherent when its underlying sheaf of modules is quasi-coherent. -/
abbrev IsQuasicoherent {X : Scheme.{u}} (F : X.Modules) : Prop :=
  SheafOfModules.IsQuasicoherent F

end AlgebraicGeometry.Scheme.Modules
