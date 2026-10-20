/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible.Discrete
public import ReasLib.RingTheory.PowerSeries.AdicTopology
public import ReasLib.AlgebraicGeometry.FormalSpectrum.Representable
public import Mathlib.Topology.Order

/-!
# Nonrepresentability of the formal spectrum of adic power series
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- The canonical map from a discrete field to its adic power series ring induces
a morphism of formal spectra that is not representable by algebraic spaces. -/
theorem not_representableByAlgebraicSpaces_spfMap_algebraMap
    {k : Type u} [Field k] [TopologicalSpace k] [DiscreteTopology k]
    [HasWeakSheafify (Scheme.fppfTopology.over (Spec (.of k))) (Type u)] :
    ¬ AlgebraicSpace.representableByAlgebraicSpaces
        ((sheafToPresheaf (Scheme.fppfTopology.over (Spec (.of k))) (Type u)).map
          (spfMap (algebraMap k (AdicPowerSeries k)) continuous_of_discreteTopology
            (CategoryTheory.Category.comp_id
              (Spec.map (CommRingCat.ofHom (algebraMap k (AdicPowerSeries k))))))) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
