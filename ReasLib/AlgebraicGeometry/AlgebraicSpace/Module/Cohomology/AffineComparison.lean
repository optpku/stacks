/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ToSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1

/-! # Affine module comparisons under cohomology vanishing -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TypeCat TopCat AlgebraicGeometry
open TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Under quasi-compactness, absolute quasi-separatedness, and vanishing first cohomology
of quasi-coherent modules, the canonical comparison from an associated affine module
to the absolute direct image of its pullback is an isomorphism. -/
instance pushforward_tensorOX {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] (M : ModuleCat.{u} (globalSectionsRing X)) :
    IsIso (tensorOXPushforwardUnit X M) :=
  sorry

/-- Under quasi-compactness, absolute quasi-separatedness, and vanishing first cohomology
of quasi-coherent modules, every module over global functions is recovered by the
canonical comparison with global sections of its associated module. -/
instance tensorOX_globalSections {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] (M : ModuleCat.{u} (globalSectionsRing X)) :
    IsIso (tensorOXSectionsUnit X M) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
