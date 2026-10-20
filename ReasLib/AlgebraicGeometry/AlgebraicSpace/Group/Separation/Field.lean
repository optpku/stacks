/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-! Absolute separatedness of decent group algebraic spaces over fields. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- A decent group algebraic space over the spectrum of a field is absolutely separated. -/
instance instIsAbsolutelySeparated {S : Scheme.{u}} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S}
    (G : GroupAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk σ)))
    [AlgebraicSpace.IsDecent G.X.left] :
    AlgebraicSpace.IsAbsolutelySeparated G.X.left := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
