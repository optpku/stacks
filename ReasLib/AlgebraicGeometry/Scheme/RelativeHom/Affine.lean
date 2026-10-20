/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeHom.Presheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AffineOver
public import ReasLib.RingTheory.FiniteFree

/-!
# Relative morphisms between affine schemes

This module records affine representability of relative-Hom presheaves under a
finite-freeness hypothesis on global sections.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.RelativeHom

/-- If `Z` and `X` are affine schemes over an affine scheme `S` and
`Γ(S, ⊤) ⟶ Γ(Z, ⊤)` is finite free, then the relative-Hom presheaf associated
to `Z` and `X` is represented by an affine scheme over `S`. -/
theorem representableByAffineOfFiniteFree {S : Scheme.{u}} [IsAffine S]
    (Z X : S.AffineOver)
    (hZ : (Hom.appTop Z.toComma.hom).hom.FiniteFree) :
    ∃ H : S.AffineOver, Nonempty ((functor Z.obj X.obj).RepresentableBy H.obj) := sorry

end AlgebraicGeometry.Scheme.RelativeHom
