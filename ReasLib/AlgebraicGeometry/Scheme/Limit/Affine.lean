/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.MorphismBaseChange

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- In a directed inverse system of quasi-compact and quasi-separated schemes with affine
transition morphisms, if a specified limit is affine, then all sufficiently late stages are
affine. -/
theorem exists_eventually_isAffine_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    [IsAffine c.pt] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsAffine (D.obj i) := sorry

/-- If the limit-to-base morphism of a directed inverse system of quasi-compact and
quasi-separated schemes with affine transition morphisms is affine, then the stage-to-base
morphisms are affine at every sufficiently late stage. -/
theorem exists_eventually_isAffineHom_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S : Scheme.{u}}
    (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    [IsAffineHom σlim] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsAffineHom (t.app i) := sorry

namespace QcqsMorphismBaseChange

/-- If a morphism becomes affine after base change to the limit of a directed inverse system,
then it becomes affine after base change to some stage mapping to the distinguished stage. -/
theorem exists_isAffineHom_stage_of_limitHom
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {D : OrderDual I ⥤ Scheme.{u}} {i0 : I} {X0 Y0 : Scheme.{u}}
    [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
    [CompactSpace X0] [QuasiSeparatedSpace X0]
    [CompactSpace Y0] [QuasiSeparatedSpace Y0]
    [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]
    (s : QcqsMorphismBaseChange D i0 X0 Y0) (h_limit : IsAffineHom s.limitHom) :
    ∃ (i : I) (hi0i : i0 ≤ i), IsAffineHom (s.stageHom i hi0i) := sorry

end QcqsMorphismBaseChange

end AlgebraicGeometry.Scheme.Limit
