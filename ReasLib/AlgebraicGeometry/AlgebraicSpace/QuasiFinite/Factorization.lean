/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Factorizations of quasi-finite morphisms of algebraic spaces

A quasi-finite separated morphism of algebraic spaces with quasi-compact,
absolutely quasi-separated target factors as a quasi-compact open immersion
followed by a finite morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- A quasi-finite separated morphism of algebraic spaces over a scheme with
quasi-compact, absolutely quasi-separated target factors as a quasi-compact
open immersion followed by a finite morphism. -/
@[stacks 082K]
theorem QuasiFinite.exists_openImmersion_finiteFactorization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiFinite f] [Separated f] [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y] :
    ∃ (T : AlgebraicSpace S) (j : X ⟶ T) (π : T ⟶ Y),
      QuasiCompact j ∧ IsOpenImmersion j ∧ IsFinite π ∧ j ≫ π = f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
