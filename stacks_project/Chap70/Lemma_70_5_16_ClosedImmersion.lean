module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_FiniteType

/-!
# Relative closed-immersion descent along directed closed limits of algebraic spaces

If a specified inverse limit of quasi-compact, absolutely quasi-separated algebraic
spaces over a quasi-compact quasi-separated algebraic space, with closed-immersion
transitions and locally finite-type stage morphisms, is a closed immersion over that
base, then all sufficiently late stages are closed immersions over the base.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit

/-- If the limit-to-base morphism of a directed inverse system of quasi-compact and
absolutely quasi-separated algebraic spaces over a quasi-compact quasi-separated
algebraic space is a closed immersion, with closed-immersion transitions and
locally finite-type stage-to-base morphisms, then the stage-to-base morphisms are
closed immersions at every sufficiently late stage. -/
theorem exists_eventually_isClosedImmersion_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ Y)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [∀ i : I, IsQuasiCompact (D.obj i)]
    [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), AlgebraicSpace.IsClosedImmersion (D.map (homOfLE hii'))]
    [∀ i : I, AlgebraicSpace.LocallyOfFiniteType (t.app i)]
    [AlgebraicSpace.IsClosedImmersion σlim] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → AlgebraicSpace.IsClosedImmersion (t.app i) := sorry

/-- If the limit-to-base morphism of a directed inverse system of quasi-compact and
absolutely quasi-separated algebraic spaces over a quasi-compact quasi-separated
algebraic space is a closed immersion, with closed-immersion transitions and
locally finite-type stage-to-base morphisms, then some stage-to-base morphism is a
closed immersion. -/
theorem exists_isClosedImmersion_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ Y)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [∀ i : I, IsQuasiCompact (D.obj i)]
    [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), AlgebraicSpace.IsClosedImmersion (D.map (homOfLE hii'))]
    [∀ i : I, AlgebraicSpace.LocallyOfFiniteType (t.app i)]
    [AlgebraicSpace.IsClosedImmersion σlim] :
    ∃ i : I, AlgebraicSpace.IsClosedImmersion (t.app i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit
