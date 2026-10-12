/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Limit.Affine

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Limit

/-- For a directed inverse system of quasi-compact and quasi-separated schemes over a
quasi-compact and quasi-separated base, with closed-immersion transition morphisms and locally
finite-type stage morphisms, a closed-immersion limit morphism forces all sufficiently late stage
morphisms to be closed immersions. -/
theorem exists_eventually_isClosedImmersion_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)] {S : Scheme.{u}}
    (D : OrderDual I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ S)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [∀ i : I, CompactSpace (D.obj i)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ i : I, LocallyOfFiniteType (t.app i)]
    [∀ {i i' : I} (hii' : i ≤ i'), IsClosedImmersion (D.map (homOfLE hii'))]
    [IsClosedImmersion σlim] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsClosedImmersion (t.app i) := sorry

namespace QcqsMorphismBaseChange

/-- If a locally finite-type morphism becomes a closed immersion after base change to the limit
of a directed inverse system, then it becomes a closed immersion after base change to some stage
above the distinguished stage. -/
theorem exists_isClosedImmersion_stage_of_limitHom
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {D : OrderDual I ⥤ Scheme.{u}} {i0 : I} {X0 Y0 : Scheme.{u}}
    [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
    [CompactSpace X0] [QuasiSeparatedSpace X0]
    [CompactSpace Y0] [QuasiSeparatedSpace Y0]
    [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]
    (s : QcqsMorphismBaseChange D i0 X0 Y0)
    (h_limit : IsClosedImmersion s.limitHom) (h_finiteType : LocallyOfFiniteType s.hom) :
    ∃ (i : I) (hi0i : i0 ≤ i), IsClosedImmersion (s.stageHom i hi0i) := sorry

end QcqsMorphismBaseChange

end AlgebraicGeometry.Scheme.Limit
