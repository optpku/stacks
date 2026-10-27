/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Compactness.Compact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf

/-!
# Quasi-compact algebraic spaces on a chosen big fppf site

A sheaf on `(Sch/S)_fppf` is a quasi-compact algebraic space when it is an
algebraic space and admits a relatively étale locally surjective atlas from a
sheafified representable of a quasi-compact object of the site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- A sheaf on `(Sch/S)_fppf` is a quasi-compact algebraic space when it is an
algebraic space and admits a relatively étale locally surjective atlas from a
quasi-compact object of the site. -/
class IsQuasiCompact {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsAlgebraicSpace X where
  /-- There is a relatively étale locally surjective atlas from a sheafified
  representable of a quasi-compact object of `(Sch/S)_fppf`. -/
  exists_compact_etaleCover :
    ∃ (U : 𝒮.bigSite S)
      (p : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X),
        relativelyEtale p ∧ Sheaf.IsLocallySurjective p ∧
          CompactSpace ((𝒮.bigToScheme S).obj U)

/-- The sheafified representable of a quasi-compact object of `(Sch/S)_fppf` is
a quasi-compact algebraic space, via the identity atlas. -/
instance instIsQuasiCompact_sheafifiedRepresentable
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigSite S) [CompactSpace ((𝒮.bigToScheme S).obj U)] :
    IsQuasiCompact ((𝒮.bigTopology S).sheafifiedRepresentable U) := sorry

namespace IsQuasiCompact

/-- A sheaf is a quasi-compact algebraic space iff it is an algebraic space and
admits a relatively étale locally surjective atlas from a quasi-compact object
of the site. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsQuasiCompact X ↔
      IsAlgebraicSpace X ∧
        ∃ (U : 𝒮.bigSite S)
          (p : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X),
            relativelyEtale p ∧ Sheaf.IsLocallySurjective p ∧
              CompactSpace ((𝒮.bigToScheme S).obj U) := sorry

/-- A quasi-compact algebraic space unpacks as an algebraic space together with
a relatively étale locally surjective atlas from a quasi-compact object of the
site. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsQuasiCompact X] :
    IsAlgebraicSpace X ∧
      ∃ (U : 𝒮.bigSite S)
        (p : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X),
          relativelyEtale p ∧ Sheaf.IsLocallySurjective p ∧
            CompactSpace ((𝒮.bigToScheme S).obj U) := sorry

/-- A relatively étale locally surjective atlas from a quasi-compact object of
the site witnesses that an algebraic space is quasi-compact. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsAlgebraicSpace X]
    {U : 𝒮.bigSite S} (p : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
    (h_etale : relativelyEtale p) (h_surj : Sheaf.IsLocallySurjective p)
    [CompactSpace ((𝒮.bigToScheme S).obj U)] : IsQuasiCompact X := sorry

end IsQuasiCompact

end AlgebraicGeometry.ChosenBigFppfSite
