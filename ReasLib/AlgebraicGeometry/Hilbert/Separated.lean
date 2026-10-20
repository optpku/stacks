/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Hilbert.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Hilbert

/-- If `X ⟶ S` is separated and the degree-`d` Hilbert functor is representable,
then its chosen representing scheme is separated over `S`. -/
@[instance]
theorem representingScheme_isSeparated {S : Scheme.{u}} (X : Over S) (d : ℕ)
    [IsSeparated X.hom] [(functor X d).IsRepresentable] :
    IsSeparated (functor X d).reprX.hom := sorry

end AlgebraicGeometry.Hilbert
