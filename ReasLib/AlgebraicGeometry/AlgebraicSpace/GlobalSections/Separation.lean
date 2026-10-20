/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.ToSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase.Equivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-! # Separation from vanishing of first cohomology -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact, absolutely quasi-separated algebraic space with vanishing first
cohomology for every quasi-coherent module is absolutely separated. -/
instance isAbsolutelySeparated_of_hasVanishingH1 {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] : IsAbsolutelySeparated X :=
  sorry

/-- The absolute canonical morphism to the spectrum of global sections of a quasi-compact,
absolutely quasi-separated algebraic space with vanishing first cohomology for every
quasi-coherent module is separated. -/
instance separated_toSpecA {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] :
    Separated
      (extendBaseMap (specULiftZIsTerminal.from S) (toSpecGamma X) ≫
        (extendBasePresheafYonedaIso (specULiftZIsTerminal.from S) (specGammaOver X)).hom ≫
        ofOverMap ((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).counit.app
          (overSpecZ (Spec (globalSectionsRing X))))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
