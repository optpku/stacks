/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-!
# Formal smoothness along étale vertical arrows

In a commutative square of algebraic spaces, étale vertical arrows transport
formal smoothness from the bottom morphism to the top morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-- In a commutative square of algebraic spaces over a scheme, if the vertical
arrows are étale and the bottom arrow is formally smooth, then the top arrow
is formally smooth. -/
theorem of_etale_commSq {S : Scheme.{u}} {U V X Y : AlgebraicSpace S}
    {ψ : U ⟶ V} {a : U ⟶ X} {b : V ⟶ Y} {f : X ⟶ Y}
    [AlgebraicSpace.Etale a] [AlgebraicSpace.Etale b] [FormallySmooth f]
    (sq : CommSq ψ a b f) : FormallySmooth ψ := sorry

end AlgebraicGeometry.AlgebraicSpace.FormallySmooth
