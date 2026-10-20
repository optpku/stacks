/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Limit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion

/-!
# Closed immersions of directed affine inverse limits

A morphism of directed inverse systems of algebraic spaces with affine
transitions and stagewise closed immersions induces a closed immersion of
limits.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits (IsLimit Cone)

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DirectedAffine

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D D' : OrderDual I ⥤ AlgebraicSpace S}
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D'.map (homOfLE h))]

/-- The morphism induced by a natural transformation of directed affine inverse
systems of algebraic spaces over `S` between arbitrary limit cones is a closed
immersion, provided each stage map is a closed immersion. -/
theorem isClosedImmersion_map (α : D ⟶ D')
    [∀ i : OrderDual I, IsClosedImmersion (α.app i)] {c : Cone D}
    {c' : Cone D'} (hc : IsLimit c) (hc' : IsLimit c') :
    IsClosedImmersion (hc'.map c α) := sorry

/-- A natural transformation between directed inverse systems of algebraic
spaces over `S` with affine transition maps and closed-immersion components
induces a closed immersion between their inverse limits. -/
@[stacks 0CUH]
instance isClosedImmersion_limMap (α : D ⟶ D')
    [∀ i : OrderDual I, IsClosedImmersion (α.app i)] :
    IsClosedImmersion (Limits.limMap α) := sorry

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
