module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A directed inverse diagram of Noetherian algebraic spaces with affine transitions and a
specified limit cone. -/
def IsNoetherianAffineLimitSystem {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] {S : Scheme.{u}}
    (D : OrderDual I ⥤ AlgebraicSpace S) (c : Cone D) (hc : IsLimit c) : Prop :=
  (∀ j : I, IsNoetherian (D.obj j)) ∧
    ∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))

end AlgebraicGeometry.AlgebraicSpace
