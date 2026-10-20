/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.OpenCover

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of

/-- A separated finite-type morphism to a quasi-compact and quasi-separated scheme admits a
Nagata compactification over its base. -/
theorem nonempty_of_finiteType {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [Scheme.Hom.FiniteType f] [IsSeparated f] :
    Nonempty (Of S (Over.mk f)) := sorry

end AlgebraicGeometry.Scheme.Compactification.Of
