/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Scheme representability of locally quasi-finite separated algebraic spaces

A separated, locally quasi-finite morphism of algebraic spaces with
scheme-representable target has scheme-representable source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsScheme

/-- A separated morphism of algebraic spaces with scheme-representable target
has scheme-representable source if it is locally of finite type and locally
quasi-finite. These two hypotheses together express local quasi-finiteness in
the Stacks convention. -/
theorem of_locallyQuasiFinite_separated {S : Scheme.{u}} {X T : AlgebraicSpace S}
    (f : X ⟶ T) [IsScheme T] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [Separated f] : IsScheme X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsScheme
