/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.MorphismBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
variable {X0 Y0 : AlgebraicSpace S}
variable [IsQuasiCompact (D.obj i0)] [IsAbsolutelyQuasiSeparated (D.obj i0)]
variable [IsQuasiCompact X0] [IsAbsolutelyQuasiSeparated X0]
variable [IsQuasiCompact Y0] [IsAbsolutelyQuasiSeparated Y0]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- Let a morphism between quasi-compact, absolutely quasi-separated algebraic spaces
lie over a quasi-compact, absolutely quasi-separated distinguished stage of a directed
inverse system with affine transition morphisms. If the morphism is locally of finite
type and its base change to the specified limit is a closed immersion, then its base
change to some stage above the distinguished stage is a closed immersion. -/
theorem exists_isClosedImmersion_stage_of_limitHom
    (s : QcqsMorphismBaseChange D i0 X0 Y0)
    (h_limit : AlgebraicSpace.IsClosedImmersion s.limitHom)
    (h_finiteType : AlgebraicSpace.LocallyOfFiniteType s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      AlgebraicSpace.IsClosedImmersion (s.stageHom i hi0i) := sorry

end AlgebraicGeometry.AlgebraicSpace.Limit.QcqsMorphismBaseChange

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
    ∃ i : I, AlgebraicSpace.IsClosedImmersion (t.app i) := by
  obtain ⟨i₀, hi₀⟩ :=
    exists_eventually_isClosedImmersion_to_base_of_isLimit D t c hc σlim hπ
  exact ⟨i₀, hi₀ le_rfl⟩

end AlgebraicGeometry.AlgebraicSpace.Limit
