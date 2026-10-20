/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flat

/-- The structural morphism of an algebraic space over the spectrum of a field is flat. -/
instance toBaseOfField {k : Type u} [Field k] (X : AlgebraicSpace (Spec (.of k))) :
    Flat (SchemeRealization.toBase X) := sorry

end AlgebraicGeometry.AlgebraicSpace.Flat
