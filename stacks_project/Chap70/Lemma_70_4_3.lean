module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.ClosedImmersion
import StacksCheckRecall

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

/- Lemma 70.4.3: Let `S` be a scheme. Let `I` be a directed set. Let
`(X_i, f_{i'i}) ⟶ (Y_i, g_{i'i})` be a morphism of inverse systems over `I`
of algebraic spaces over `S`. Assume the morphisms `f_{i'i} : X_{i'} ⟶ X_i`
are affine, the morphisms `g_{i'i} : Y_{i'} ⟶ Y_i` are affine, and the
morphisms `X_i ⟶ Y_i` are closed immersions. Then `lim X_i ⟶ lim Y_i` is a
closed immersion. -/
@[stacks 0CUH] #check (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.isClosedImmersion_limMap :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {D D' : OrderDual I ⥤ AlgebraicSpace S}
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      [∀ {i i' : I} (h : i ≤ i'), Affine (D'.map (homOfLE h))]
      (α : D ⟶ D') [∀ i : OrderDual I, IsClosedImmersion (α.app i)],
      IsClosedImmersion (Limits.limMap α))

#check (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.isClosedImmersion_map :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} {D D' : OrderDual I ⥤ AlgebraicSpace S}
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      [∀ {i i' : I} (h : i ≤ i'), Affine (D'.map (homOfLE h))]
      (α : D ⟶ D') [∀ i : OrderDual I, IsClosedImmersion (α.app i)]
      {c : Cone D} {c' : Cone D'} (hc : IsLimit c) (hc' : IsLimit c'),
      IsClosedImmersion (hc'.map c α))
