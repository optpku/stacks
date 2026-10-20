module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Pullback

/-!
# Finite-presentation descent of algebraic stacks along directed affine limits

Algebraic stacks of finite presentation over a directed inverse limit of
quasi-compact, absolutely quasi-separated algebraic spaces with affine
transition maps descend to some stage.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Limit.FinitePresentation

/-- Every algebraic stack of finite presentation over a directed affine limit of
quasi-compact, absolutely quasi-separated algebraic spaces descends to a finitely
presented algebraic stack over some stage, whose 2-fibre product with the limit
is equivalent to the original stack over the limit. -/
theorem exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, AlgebraicSpace.IsQuasiCompact (D.obj j)]
    [∀ j, AlgebraicSpace.IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), AlgebraicSpace.Affine (D.map (homOfLE hjj'))]
    {X : GroupoidsOver S} [AlgebraicStack X]
    (f : X ⟶ c.pt.toGroupoids) [AlgebraicStack.FinitePresentation f] :
    ∃ (i : I) (Xi : GroupoidsOver S) (hXi : AlgebraicStack Xi)
      (fi : Xi ⟶ (D.obj i).toGroupoids)
      (hfi : AlgebraicStack.FinitePresentation fi)
      (e : X ≌ AlgebraicStack.pullback fi (c.π.app i)),
      Nonempty (e.hom ≫ AlgebraicStack.pullbackSnd fi (c.π.app i) ≅ f) := sorry

end AlgebraicGeometry.AlgebraicStack.Limit.FinitePresentation
