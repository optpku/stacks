/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.QuasiSeparated
public import stacks_project.Chap87.Lemma_87_16_1_Pullback

/-!
# Quasi-separated algebraic spaces on a chosen big fppf site

A sheaf on `(Sch/S)_fppf` is a quasi-separated algebraic space when it is an
algebraic space and fibre products of morphisms from quasi-compact schemes
into it are quasi-compact.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- A sheaf on `(Sch/S)_fppf` is a quasi-separated algebraic space when it is
an algebraic space and fibre products of morphisms from quasi-compact schemes
to it are quasi-compact. -/
class IsQuasiSeparated {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsAlgebraicSpace X where
  /-- Fibre products of morphisms from quasi-compact schemes to `X` are
  quasi-compact. -/
  quasiCompact_pullback : forallQuasiCompactPullback X

namespace IsQuasiSeparated

/-- The sheafified representable of a quasi-separated object of `(Sch/S)_fppf`
is a quasi-separated algebraic space. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigSite S) [QuasiSeparatedSpace ((𝒮.bigToScheme S).obj U)] :
    IsQuasiSeparated ((𝒮.bigTopology S).sheafifiedRepresentable U) where
  quasiCompact_pullback := sorry

/-- A sheaf is a quasi-separated algebraic space iff it is an algebraic space
and fibre products of morphisms from quasi-compact schemes to it are
quasi-compact. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsQuasiSeparated X ↔
      IsAlgebraicSpace X ∧ forallQuasiCompactPullback X := sorry

/-- A quasi-separated algebraic space unpacks as an algebraic space together
with quasi-compact fibre products of morphisms from quasi-compact schemes. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsQuasiSeparated X] :
    IsAlgebraicSpace X ∧ forallQuasiCompactPullback X := sorry

/-- Quasi-compact fibre products of morphisms from quasi-compact schemes
witness that an algebraic space sheaf is quasi-separated. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsAlgebraicSpace X]
    (h : forallQuasiCompactPullback X) : IsQuasiSeparated X := sorry

/-- If `X` is a quasi-separated algebraic space, then fibre products of
morphisms from quasi-compact schemes to `X` are quasi-compact. -/
theorem isQuasiCompact_pullback {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsQuasiSeparated X]
    {U V : 𝒮.bigSite S}
    [CompactSpace ((𝒮.bigToScheme S).obj U)]
    [CompactSpace ((𝒮.bigToScheme S).obj V)]
    (u : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
    (v : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) :
    IsQuasiCompact (pullback u v) := sorry

/-- An algebraic space sheaf satisfying the affine fibre-product tests is
quasi-separated. -/
theorem of_forallAffineQuasiCompactPullback {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsAlgebraicSpace X]
    (h : forallAffineQuasiCompactPullback X) : IsQuasiSeparated X := sorry

end IsQuasiSeparated

end AlgebraicGeometry.ChosenBigFppfSite
