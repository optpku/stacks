/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety
public import ReasLib.AlgebraicGeometry.GroupScheme.QuasiProjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Comparison

@[expose] public section

universe u

namespace AlgebraicGeometry.AbelianVariety

/-- The structure morphism of an abelian variety over a field is projective. -/
instance instProjective {k : Type u} [Field k] (A : SchemeOverField k)
    [CategoryTheory.GrpObj A] [AlgebraicGeometry.AbelianVariety A] : Projective A.hom := sorry

end AlgebraicGeometry.AbelianVariety
