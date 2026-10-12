/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Torsion.Exact
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Affine
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Torsion-free modules in short exact sequences

Torsion-free quasicoherent module sheaves on integral schemes are closed under extensions.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsTorsionFree

variable {X : Scheme.{u}} [IsIntegral X]
variable {S : ShortComplex X.Modules}
variable [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]

/-- In a short exact complex of quasicoherent module sheaves on an integral scheme,
torsion-freeness of the outer terms implies torsion-freeness of the middle term. -/
@[stacks 0AXX "torsion-free quasicoherent modules are closed under extensions"]
theorem middle_of_shortExact
    (hS : S.ShortExact) [IsTorsionFree S.X₁] [IsTorsionFree S.X₃] :
    IsTorsionFree S.X₂ := sorry

end AlgebraicGeometry.Scheme.Modules.IsTorsionFree
