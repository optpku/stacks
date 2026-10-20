/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-! # Global sections of spectrum base changes under cohomology vanishing -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For a quasi-compact, absolutely quasi-separated algebraic space with vanishing
first cohomology on quasi-coherent modules, the canonical map from any base-change
ring to global sections of the spectrum base change is an isomorphism. -/
instance globalSectionsRing_baseChangeSpec {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] {A' : CommRingCat.{u}} (φ : globalSectionsRing X ⟶ A') :
    IsIso (baseChangeSpecGlobalSectionsMap X φ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
