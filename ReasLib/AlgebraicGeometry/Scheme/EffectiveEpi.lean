/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.CategoryTheory.Sites.Family.UniversalEffectiveEpi

/-!
# Effective epimorphic families of schemes

This file records criteria for families of scheme morphisms to be universally effective
epimorphic.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

namespace CategoryTheory.SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily

/-- A family of scheme morphisms is universally effective epimorphic if every base change
to an affine scheme is effective epimorphic. -/
theorem of_affine {X : Scheme.{u}} (K : Over.{v} X)
    (h_affine : ∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ X),
      IsEffectiveEpiFamily (K.baseChange f)) :
    IsUniversalEffectiveEpiFamily K := sorry

end CategoryTheory.SemiRepresentableFamily.Over.IsUniversalEffectiveEpiFamily
