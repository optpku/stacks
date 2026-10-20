/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

/-!
# Absolute quasi-separatedness of locally Noetherian decent algebraic spaces

Locally Noetherian decent algebraic spaces are absolutely quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsAbsolutelyQuasiSeparated

/-- A locally Noetherian decent algebraic space is absolutely quasi-separated. -/
@[stacks 0BB6]
instance of_isLocallyNoetherian_isDecent {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsLocallyNoetherian X] [IsDecent X] :
    IsAbsolutelyQuasiSeparated X := sorry

end IsAbsolutelyQuasiSeparated

end AlgebraicGeometry.AlgebraicSpace
