/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.CompactOpens
public import ReasLib.AlgebraicGeometry.Scheme.Limit.ClosedImmersion

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- A closed immersion into the limit of a directed inverse system of quasi-compact schemes
with affine transition morphisms is a closed immersion into every sufficiently large stage,
provided its source is locally of finite type over the base scheme. -/
theorem exists_eventually_isClosedImmersion_to_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S Y : Scheme.{u}}
    (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    (f : Y ⟶ c.pt) (g : Y ⟶ S) [IsClosedImmersion f] [LocallyOfFiniteType g]
    (hfg : f ≫ σlim = g) :
    ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → IsClosedImmersion (f ≫ c.π.app i') := sorry

/-- An immersion into the limit of a directed inverse system of quasi-separated schemes with
affine transition morphisms is an immersion into every sufficiently large stage, provided its
source is quasi-compact and locally of finite type over the base scheme. -/
theorem exists_eventually_isImmersion_to_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S Y : Scheme.{u}}
    (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]
    [CompactSpace Y]
    (f : Y ⟶ c.pt) (g : Y ⟶ S) [IsImmersion f] [LocallyOfFiniteType g]
    (hfg : f ≫ σlim = g) :
    ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → IsImmersion (f ≫ c.π.app i') := sorry

/-- An isomorphism to the limit of a directed inverse system with closed-immersion transition
morphisms is an isomorphism to every sufficiently large stage when the stages are quasi-compact
and locally of finite type over the base and the source is locally of finite presentation over
the base. -/
theorem exists_eventually_isIso_to_stage
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S Y : Scheme.{u}}
    (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, LocallyOfFiniteType (t.app i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsClosedImmersion (D.map (homOfLE hii'))]
    (f : Y ⟶ c.pt) (g : Y ⟶ S) [IsIso f] [LocallyOfFinitePresentation g]
    (hfg : f ≫ σlim = g) :
    ∃ i : I, ∀ ⦃i' : I⦄, i ≤ i' → IsIso (f ≫ c.π.app i') := sorry

/-- For a directed inverse system of quasi-compact and quasi-separated schemes over a
quasi-separated base, with closed-immersion transition morphisms and locally finite-type stage
morphisms, an immersion from the limit to the base forces all sufficiently late stage morphisms
to be immersions. -/
theorem exists_eventually_isImmersion_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S : Scheme.{u}}
    (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [QuasiSeparatedSpace S]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ i : I, LocallyOfFiniteType (t.app i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsClosedImmersion (D.map (homOfLE hii'))]
    [IsImmersion σlim] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsImmersion (t.app i) := sorry

namespace QcqsMorphismBaseChange

/-- If a locally finite-type morphism becomes an immersion after base change to the limit of a
directed inverse system, then it becomes an immersion after base change to some stage above the
distinguished stage. -/
theorem exists_isImmersion_stage_of_limitHom
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {D : OrderDual I ⥤ Scheme.{u}} {i0 : I} {X0 Y0 : Scheme.{u}}
    [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
    [CompactSpace X0] [QuasiSeparatedSpace X0]
    [CompactSpace Y0] [QuasiSeparatedSpace Y0]
    [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]
    (s : QcqsMorphismBaseChange D i0 X0 Y0)
    (h_limit : IsImmersion s.limitHom) (h_finiteType : LocallyOfFiniteType s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), IsImmersion (s.stageHom i hi0i) := sorry

end QcqsMorphismBaseChange

end AlgebraicGeometry.Scheme.Limit
