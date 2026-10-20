/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ResolutionProperty

/-!
# Resolution property of directed affine limits of algebraic spaces

A specified inverse limit of quasi-compact, absolutely quasi-separated algebraic
spaces over a scheme with affine transition morphisms has the resolution property
if and only if some stage does.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit

/-- A specified inverse limit of quasi-compact and absolutely quasi-separated
algebraic spaces over a scheme with affine transition morphisms has the
resolution property if and only if some stage does. -/
@[stacks 0GV2]
theorem hasResolutionProperty_iff_exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ i, IsQuasiCompact (D.obj i)]
    [∀ i, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))] :
    SheafOfModules.HasResolutionProperty (structureSheaf c.pt) ↔
      ∃ i : I, SheafOfModules.HasResolutionProperty (structureSheaf (D.obj i)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit
