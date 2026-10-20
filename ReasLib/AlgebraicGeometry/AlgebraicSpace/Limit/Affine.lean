/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.MorphismBaseChange

/-!
# Affineness descent along directed affine limits of algebraic spaces

If a specified inverse limit of quasi-compact, absolutely quasi-separated algebraic
spaces with affine transitions is affine, then all sufficiently late stages are
affine. If such a system has compatible morphisms to a quasi-compact, absolutely
quasi-separated algebraic space and the limit-to-base morphism is affine, then
all sufficiently late stage-to-base morphisms are affine. Affineness of a
base-changed morphism to the limit also descends to a stage.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit

/-- In a directed inverse system of quasi-compact and absolutely quasi-separated
algebraic spaces with affine transition morphisms, if a specified limit is
affine, then all sufficiently late stages are affine. -/
theorem exists_eventually_isAffine_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    [AlgebraicSpace.IsAffine c.pt] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → AlgebraicSpace.IsAffine (D.obj i) := sorry

/-- If a specified inverse limit of quasi-compact and absolutely quasi-separated
algebraic spaces with affine transition morphisms is affine, then some stage is
affine. -/
theorem exists_isAffine_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    [AlgebraicSpace.IsAffine c.pt] :
    ∃ i : I, AlgebraicSpace.IsAffine (D.obj i) := by
  obtain ⟨i₀, hi₀⟩ := exists_eventually_isAffine_of_isLimit D c hc
  exact ⟨i₀, hi₀ (le_refl i₀)⟩

/-- If the limit-to-base morphism of a directed inverse system of quasi-compact and
absolutely quasi-separated algebraic spaces over a quasi-compact quasi-separated
algebraic space is affine, then the stage-to-base morphisms are affine at every
sufficiently late stage. -/
theorem exists_eventually_isAffine_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ Y)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [∀ i : I, IsQuasiCompact (D.obj i)]
    [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
    [Affine σlim] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → Affine (t.app i) := sorry

/-- If the limit-to-base morphism of a directed inverse system of quasi-compact and
absolutely quasi-separated algebraic spaces over a quasi-compact quasi-separated
algebraic space is affine, then some stage-to-base morphism is affine. -/
theorem exists_isAffine_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ Y)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    [∀ i : I, IsQuasiCompact (D.obj i)]
    [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
    [Affine σlim] :
    ∃ i : I, Affine (t.app i) := by
  obtain ⟨i₀, hi₀⟩ := exists_eventually_isAffine_to_base_of_isLimit D t c hc σlim hπ
  exact ⟨i₀, hi₀ le_rfl⟩

end AlgebraicGeometry.AlgebraicSpace.Limit

namespace AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
variable {X0 Y0 : AlgebraicSpace S}
variable [IsQuasiCompact (D.obj i0)] [IsAbsolutelyQuasiSeparated (D.obj i0)]
variable [IsQuasiCompact X0] [IsAbsolutelyQuasiSeparated X0]
variable [IsQuasiCompact Y0] [IsAbsolutelyQuasiSeparated Y0]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- If a morphism between quasi-compact, absolutely quasi-separated algebraic spaces
becomes affine after base change to a specified directed inverse limit, then it
becomes affine after base change to some stage above the distinguished stage. -/
theorem exists_affine_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0)
    (h_limit : AlgebraicSpace.Affine s.limitHom) :
    ∃ (i : I) (hi0i : i0 ≤ i), AlgebraicSpace.Affine (s.stageHom i hi0i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange
