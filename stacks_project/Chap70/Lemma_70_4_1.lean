module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Limit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Pullback
import StacksCheckRecall

/-!
# Lemma 70.4.1

A directed inverse system of algebraic spaces with affine transitions has an
inverse limit, affine projections, and fibre products commuting with the
directed limit over a cofinal tail.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits (IsLimit)

universe u

/- Lemma 70.4.1: A directed inverse system of algebraic spaces with affine
transitions has an algebraic-space fppf limit, affine projections, and fibre
products commuting with the inverse limit over every cofinal tail. -/
@[stacks 07SF] #check (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.limit_functorOfPoints :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      [h_affine : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))],
      (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.limit D).functorOfPoints =
        Limits.limit (D ⋙ AlgebraicGeometry.AlgebraicSpace.forgetToPresheaf))

#check (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.affine_π :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      [h_affine : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))],
      ∀ (i : OrderDual I), Affine (Limits.limit.π D i))

#check (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.isLimit_pullbackCone :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      [h_affine : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))],
      ∀ (i : I) {T : AlgebraicSpace S} (g : T ⟶ D.obj (OrderDual.toDual i)),
        IsLimit (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.pullbackCone D i g))
