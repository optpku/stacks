/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Reflexive
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Affine
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Reflexive modules in exact sequences

The kernel term of an exact complex of coherent module sheaves is reflexive when the middle term
is reflexive and the target is torsion-free.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsReflexive

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable {S : ShortComplex X.Modules}
variable [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]

/-- In an exact complex of coherent module sheaves on an integral locally Noetherian scheme,
monicity of the first map, reflexivity of the middle term, and torsion-freeness of the target
imply reflexivity of the source. -/
@[stacks 0EBG "reflexivity of the source in an exact complex"]
theorem left_of_exact
    (hS : S.Exact) [Mono S.f] [IsReflexive S.X₂] [IsTorsionFree S.X₃] :
    IsReflexive S.X₁ := sorry

end AlgebraicGeometry.Scheme.Modules.IsReflexive
