module

public import stacks_project.Chap70.Lemma_70_5_4_PointClosure
public import stacks_project.Chap70.Lemma_70_5_4_Limit
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.5.4 (1): Let `S` be a scheme. Let `X = lim_i X_i` be the limit of a
directed inverse system of algebraic spaces over `S` with affine transition
morphisms (Lemma 70.4.1). Let `x ∈ |X|` with images `x_i ∈ |X_i|`. If each
`X_i` is decent, then `closure {x} = lim_i closure {x_i}` as sets, as
membership in `PointClosure.closedSubset` along the cone projections. -/
@[stacks 0CUK] #check
  (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.mem_closure_iff :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      [∀ i : OrderDual I, IsDecent (D.obj i)]
      (c : Cone D) (_ : IsLimit c) (x y : Points c.pt),
      y ∈ (PointClosure.closedSubset x : Set (Points c.pt)) ↔
        ∀ i : OrderDual I,
          Points.map (c.π.app i) y ∈
            (PointClosure.closedSubset (Points.map (c.π.app i) x) :
              Set (Points (D.obj i))))

/- Lemma 70.5.4 (2): With the same notation and assumptions, the equality
`closure {x} = lim_i closure {x_i}` also holds as algebraic spaces after
endowing both sides with the reduced induced structure, as
`Nonempty (IsLimit (pointClosureCone D c x))` with apex
`PointClosure.space x`. -/
@[stacks 0CUK] #check
  (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.nonempty_isLimit_pointClosureCone :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      [∀ i : OrderDual I, IsDecent (D.obj i)]
      (c : Cone D) (_ : IsLimit c) (x : Points c.pt),
      Nonempty (IsLimit (DirectedAffine.pointClosureCone D c x)))
