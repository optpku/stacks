/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.UniversallyInjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 69.16.5: In Situation 69.16.1, the absolute canonical morphism
X ⟶ Spec Γ(X, 𝒪_X) is universally injective. -/
@[stacks 07V4] #check
  (AlgebraicGeometry.AlgebraicSpace.universallyInjective_toSpecA :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
      [HasVanishingH1 X], UniversallyInjective (toSpecA X))

#check (AlgebraicGeometry.AlgebraicSpace.toSpecA :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    extendBase (specULiftZIsTerminal.from S) X ⟶
      ofOver (overSpecZ (Spec (globalSectionsRing X))))

#check (AlgebraicGeometry.AlgebraicSpace.toSpecA_eq :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    toSpecA X =
      NatTrans.vcomp
        (extendBasePresheafMap (specULiftZIsTerminal.from S) (toSpecGamma X))
        (NatTrans.vcomp
          (extendBasePresheafYonedaIso (specULiftZIsTerminal.from S) (specGammaOver X)).hom
          (ofOverMap
            ((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).counit.app
              (overSpecZ (Spec (globalSectionsRing X)))))))

#check (AlgebraicGeometry.AlgebraicSpace.specMapSpecZ :
  ∀ {R R' : CommRingCat.{u}} (φ : R ⟶ R'),
    ofOver (overSpecZ (Spec R')) ⟶ ofOver (overSpecZ (Spec R)))

#check (AlgebraicGeometry.AlgebraicSpace.specMapSpecZ_eq :
  ∀ {R R' : CommRingCat.{u}} (φ : R ⟶ R'),
    specMapSpecZ φ = ofOverMap (Over.homMk (Spec.map φ) (specMap_w φ)))

#check (AlgebraicGeometry.AlgebraicSpace.subsingleton_points_toSpecAFiber :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] {K : Type u} [Field K]
    (φ : globalSectionsRing X ⟶ CommRingCat.of K),
    Subsingleton (Points (pullback (specMapSpecZ φ) (toSpecA X))))
