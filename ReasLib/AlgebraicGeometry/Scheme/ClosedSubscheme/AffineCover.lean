/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyClosed.AffineDescent

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme covered on its underlying topological space by finitely many affine closed
subschemes is affine. -/
theorem isAffine_of_finite_affine_closedSubscheme_cover
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (Z : ι → X.IdealSheafData)
    [∀ j, IsAffine (Z j).subscheme]
    (hcover : ∀ x : X, ∃ j : ι, x ∈ (Z j).support) :
    IsAffine X := sorry

end AlgebraicGeometry.Scheme
