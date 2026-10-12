/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_45_2_Integral

/-!
# Relative finiteness descent along directed finite limits of algebraic spaces

If a specified inverse limit of quasi-compact, absolutely quasi-separated algebraic
spaces over a quasi-compact quasi-separated algebraic space, with finite transitions
and locally finite-type stage morphisms, is integral over that base, then all
sufficiently late stages are finite over the base.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit

/-- If the limit-to-base morphism of a directed inverse system of quasi-compact and
absolutely quasi-separated algebraic spaces over a quasi-compact quasi-separated
algebraic space is integral, with finite transitions and locally finite-type
stage-to-base morphisms, then the stage-to-base morphisms are finite at every
sufficiently late stage. -/
theorem exists_eventually_isFinite_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ Y)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [∀ i : I, IsQuasiCompact (D.obj i)]
    [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), AlgebraicSpace.IsFinite (D.map (homOfLE hii'))]
    [∀ i : I, AlgebraicSpace.LocallyOfFiniteType (t.app i)]
    [AlgebraicSpace.IsIntegralHom σlim] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → AlgebraicSpace.IsFinite (t.app i) := sorry

/-- If the limit-to-base morphism of a directed inverse system of quasi-compact and
absolutely quasi-separated algebraic spaces over a quasi-compact quasi-separated
algebraic space is integral, with finite transitions and locally finite-type
stage-to-base morphisms, then some stage-to-base morphism is finite. -/
theorem exists_isFinite_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ Y)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [∀ i : I, IsQuasiCompact (D.obj i)]
    [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), AlgebraicSpace.IsFinite (D.map (homOfLE hii'))]
    [∀ i : I, AlgebraicSpace.LocallyOfFiniteType (t.app i)]
    [AlgebraicSpace.IsIntegralHom σlim] :
    ∃ i : I, AlgebraicSpace.IsFinite (t.app i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit
