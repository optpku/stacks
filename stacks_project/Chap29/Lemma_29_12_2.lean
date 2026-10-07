module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family.Diagonal
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/-
Lemma 29.12.2: if every point of a scheme lies in an affine nonvanishing open of a global
section of some invertible module, then the diagonal of the scheme is affine.
-/
@[stacks 0FXS] #check
  (@AlgebraicGeometry.Scheme.Modules.isAffineHom_diagonal_of_exists_affine_nonvanishing_open :
    ∀ {X : Scheme.{u}},
      (∀ x : X,
        ∃ (L : X.Modules) (hL : Scheme.Modules.Invertible L) (s : Γ(L, ⊤)),
          Scheme.Modules.AffineOpenNeighborhood x (hL.sectionNonvanishingOpen s)) →
      IsAffineHom (pullback.diagonal (terminal.from X)))
