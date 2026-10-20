/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Separation
import StacksCheckRecall

/-!
# Lemma 69.16.6

In Situation 69.16.1, the absolute canonical morphism from `X` to the spectrum
of its ring of global sections is separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 69.16.6: in Situation 69.16.1, the absolute canonical morphism
from `X` to the spectrum of its ring of global sections is separated. -/
@[stacks 07V5]
#check (AlgebraicGeometry.AlgebraicSpace.separated_toSpecA :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X],
    Separated
      (extendBaseMap (specULiftZIsTerminal.from S) (toSpecGamma X) ≫
        (extendBasePresheafYonedaIso (specULiftZIsTerminal.from S) (specGammaOver X)).hom ≫
        ofOverMap ((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).counit.app
          (overSpecZ (Spec (globalSectionsRing X))))))

#check (AlgebraicGeometry.AlgebraicSpace.isAbsolutelySeparated_of_hasVanishingH1 :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X], IsAbsolutelySeparated X)
