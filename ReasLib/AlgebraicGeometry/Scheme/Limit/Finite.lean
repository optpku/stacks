module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- For a directed inverse system of quasi-compact and quasi-separated schemes over a
quasi-compact and quasi-separated base, with finite transition morphisms and locally
finite-type stage morphisms, an integral limit morphism forces all sufficiently late stage
morphisms to be finite. -/
theorem exists_eventually_isFinite_to_base_of_isLimit_isIntegralHom
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S : Scheme.{u}}
    (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsFinite (D.map (homOfLE hii'))]
    [∀ i : I, LocallyOfFiniteType (t.app i)]
    [IsIntegralHom σlim] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsFinite (t.app i) := sorry

namespace QcqsMorphismBaseChange

/-- If a morphism becomes finite after base change to the limit of a directed inverse system
and is locally of finite type over the distinguished stage, then it becomes finite after base
change to some stage mapping to the distinguished stage. -/
theorem exists_isFinite_stage_of_limitHom
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {D : OrderDual I ⥤ Scheme.{u}} {i0 : I} {X0 Y0 : Scheme.{u}}
    [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
    [CompactSpace X0] [QuasiSeparatedSpace X0]
    [CompactSpace Y0] [QuasiSeparatedSpace Y0]
    [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]
    (s : QcqsMorphismBaseChange D i0 X0 Y0) (h_limit : IsFinite s.limitHom)
    (h_finiteType : LocallyOfFiniteType s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), IsFinite (s.stageHom i hi0i) := sorry

end QcqsMorphismBaseChange

end AlgebraicGeometry.Scheme.Limit
