module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Nonempty
import StacksCheckRecall

/-!
# Nonemptiness of directed affine inverse limits of algebraic spaces

A directed inverse limit of nonempty quasi-compact algebraic spaces with affine
transitions is nonempty.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits (Cone IsLimit)

universe u

/- Lemma 70.5.3: Let `S` be a scheme. Let `X = lim_i X_i` be the limit of a directed
inverse system of algebraic spaces over `S` with affine transition morphisms
(Lemma 70.4.1). If each `X_i` is quasi-compact and nonempty, then `|X|` is nonempty,
as `Nonempty (Points c.pt)`. -/
@[stacks 086W] #check
  (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.nonempty_of_isLimit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      [∀ i : OrderDual I, Nonempty (Points (D.obj i))]
      [∀ i : OrderDual I, IsQuasiCompact (D.obj i)]
      (c : Cone D), IsLimit c → Nonempty (Points c.pt))

#check (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.instNonempty_points_limit :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      [∀ i : OrderDual I, Nonempty (Points (D.obj i))]
      [∀ i : OrderDual I, IsQuasiCompact (D.obj i)],
      Nonempty (Points (Limits.limit D)))
