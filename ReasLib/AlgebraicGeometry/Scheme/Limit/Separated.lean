/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Affine
import ReasLib.AlgebraicGeometry.Scheme.Limit.ClosedImmersion

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- In a directed inverse system of quasi-compact and quasi-separated schemes with affine
transition morphisms, if a specified limit is separated, then all sufficiently late stages are
separated. -/
theorem exists_eventually_isSeparated_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j)]
    [∀ j, QuasiSeparatedSpace (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    [c.pt.IsSeparated] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → (D.obj i).IsSeparated := sorry

/-- If the limit-to-base morphism of a directed inverse system of quasi-compact and
quasi-separated schemes over a quasi-separated base is separated, then the stage-to-base
morphisms are separated at every sufficiently late stage. -/
theorem exists_eventually_isSeparated_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S : Scheme.{u}}
    (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [QuasiSeparatedSpace S]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    [IsSeparated σlim] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsSeparated (t.app i) := sorry

namespace QcqsMorphismBaseChange

/-- If a morphism becomes separated after base change to the limit of a directed inverse system,
then it becomes separated after base change to some stage above the distinguished stage. -/
theorem exists_isSeparated_stage_of_limitHom
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {D : OrderDual I ⥤ Scheme.{u}} {i0 : I} {X0 Y0 : Scheme.{u}}
    [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
    [CompactSpace X0] [QuasiSeparatedSpace X0]
    [CompactSpace Y0] [QuasiSeparatedSpace Y0]
    [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]
    (s : QcqsMorphismBaseChange D i0 X0 Y0) (h_limit : IsSeparated s.limitHom) :
    ∃ (i : I) (hi0i : i0 ≤ i), IsSeparated (s.stageHom i hi0i) := sorry

end QcqsMorphismBaseChange

end AlgebraicGeometry.Scheme.Limit
