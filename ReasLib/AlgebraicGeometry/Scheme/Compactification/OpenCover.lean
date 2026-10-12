/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.ProperExtension

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of

/-- A separated finite-type scheme over a Noetherian base is compactifiable if it is
covered by two compactifiable opens whose intersection is dense. -/
theorem nonempty_of_sup_eq_top_of_dense
    {S : Scheme.{u}} [IsNoetherian S] (U : Over S)
    [Scheme.Hom.FiniteType U.hom] [IsSeparated U.hom]
    (U₁ U₂ : U.left.Opens) (hcover : U₁ ⊔ U₂ = ⊤)
    (hdense : Dense (U₁ ⊓ U₂ : Set U.left))
    [Nonempty (Of S (Over.mk (U₁.ι ≫ U.hom)))]
    [Nonempty (Of S (Over.mk (U₂.ι ≫ U.hom)))] :
    Nonempty (Of S U) := sorry

end AlgebraicGeometry.Scheme.Compactification.Of
