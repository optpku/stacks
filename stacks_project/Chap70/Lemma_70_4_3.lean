/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap70.Lemma_70_4_1_Limit

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

/-- Lemma 70.4.3: Let `S` be a scheme. Let `I` be a directed set. Let
`(X_i, f_{i'i}) ⟶ (Y_i, g_{i'i})` be a morphism of inverse systems over `I`
of algebraic spaces over `S`. Assume the morphisms `f_{i'i} : X_{i'} ⟶ X_i`
are affine, the morphisms `g_{i'i} : Y_{i'} ⟶ Y_i` are affine, and the
morphisms `X_i ⟶ Y_i` are closed immersions. Then `lim X_i ⟶ lim Y_i` is a
closed immersion. -/
@[stacks 0CUH]
instance isClosedImmersion_limMap (α : D ⟶ D')
    [∀ i : OrderDual I, IsClosedImmersion (α.app i)] :
    IsClosedImmersion (Limits.limMap α) := sorry

/-- The morphism induced by a natural transformation of directed affine inverse
systems of algebraic spaces over `S` between arbitrary limit cones is a closed
immersion, provided each stage map is a closed immersion. -/
theorem isClosedImmersion_map (α : D ⟶ D')
    [∀ i : OrderDual I, IsClosedImmersion (α.app i)] {c : Cone D}
    {c' : Cone D'} (hc : IsLimit c) (hc' : IsLimit c') :
    IsClosedImmersion (hc'.map c α) := sorry

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
