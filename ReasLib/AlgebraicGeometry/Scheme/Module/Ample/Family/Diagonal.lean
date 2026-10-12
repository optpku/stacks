/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors

/-!
# Affine diagonals from families of invertible modules

This file relates affine nonvanishing neighborhoods of sections of invertible
modules to the affineness of the diagonal morphism.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Modules

/-- If every point of a scheme has an affine nonvanishing neighborhood from a global section of
an invertible module, then the diagonal morphism of the scheme is affine. -/
theorem isAffineHom_diagonal_of_exists_affine_nonvanishing_open {X : Scheme.{u}}
    (hX : ∀ x : X, ∃ (L : X.Modules) (hL : Invertible L) (s : Γ(L, ⊤)),
      AffineOpenNeighborhood x (hL.sectionNonvanishingOpen s)) :
    IsAffineHom (pullback.diagonal (terminal.from X)) := sorry

/-- The diagonal of a scheme is affine when an indexed family of invertible modules supplies
affine nonvanishing neighborhoods at every point. -/
theorem isAffineHom_diagonal_of_affineNonvanishingFamily {X : Scheme.{u}} {ι : Type v}
    (L : ι → X.Modules) (hL : AffineNonvanishingFamily L) :
    IsAffineHom (pullback.diagonal (terminal.from X)) := sorry

end AlgebraicGeometry.Scheme.Modules
