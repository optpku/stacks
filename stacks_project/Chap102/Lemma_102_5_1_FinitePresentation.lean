module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap101.Definition_101_27_1_FinitePresentation

/-!
# Finite-presentation descent of algebraic stacks along directed affine limits

This leaf records object descent for algebraic stacks of finite presentation
over a directed inverse limit of quasi-compact, quasi-separated algebraic
spaces with affine transition maps.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Limit.FinitePresentation

/-- The 2-fibre product `𝒳_i ×_{X_i} X` of a 1-morphism of algebraic stacks to a
stage with the limit projection `X ⟶ X_i`. -/
abbrev limitPullback {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} (c : Cone D) {i : I}
    {Xi : GroupoidsOver S} (fi : Xi ⟶ (D.obj i).toGroupoids) :
    GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} fi
    (AlgebraicSpace.toGroupoids.map (c.π.app i))

/-- The projection `𝒳_i ×_{X_i} X ⟶ X`. -/
abbrev limitPullback.snd {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} (c : Cone D) {i : I}
    {Xi : GroupoidsOver S} (fi : Xi ⟶ (D.obj i).toGroupoids) :
    limitPullback c fi ⟶ c.pt.toGroupoids :=
  TwoFibreProduct.snd.{u + 1, u, u + 1, u} fi
    (AlgebraicSpace.toGroupoids.map (c.π.app i))

/-- The projection `𝒳_i ×_{X_i} X ⟶ X` is the second 2-fibre-product projection
along the limit map to the stage. -/
theorem limitPullback.snd_eq {I : Type u} [Preorder I] {S : Scheme.{u}}
    {D : OrderDual I ⥤ AlgebraicSpace S} (c : Cone D) {i : I}
    {Xi : GroupoidsOver S} (fi : Xi ⟶ (D.obj i).toGroupoids) :
    limitPullback.snd c fi =
      TwoFibreProduct.snd.{u + 1, u, u + 1, u} fi
        (AlgebraicSpace.toGroupoids.map (c.π.app i)) :=
  sorry

/-- Every algebraic stack of finite presentation over a directed affine limit of
quasi-compact, quasi-separated algebraic spaces descends to a finitely presented
algebraic stack over some stage, whose 2-fibre product with the limit is
equivalent to the original stack over the limit. -/
theorem exists_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, AlgebraicSpace.IsQuasiCompact (D.obj j)]
    [∀ j, AlgebraicSpace.IsQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), AlgebraicSpace.Affine (D.map (homOfLE hjj'))]
    {X : GroupoidsOver S} [AlgebraicStack X]
    (f : X ⟶ c.pt.toGroupoids) [AlgebraicStack.FinitePresentation f] :
    ∃ (i : I) (Xi : GroupoidsOver S) (hXi : AlgebraicStack Xi)
      (fi : Xi ⟶ (D.obj i).toGroupoids)
      (hfi : AlgebraicStack.FinitePresentation fi)
      (e : X ≌ limitPullback c fi),
      Nonempty (e.hom ≫ limitPullback.snd c fi ≅ f) := sorry

end AlgebraicGeometry.AlgebraicStack.Limit.FinitePresentation
