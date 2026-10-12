/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec
public import stacks_project.Chap69.Lemma_69_16_3_BaseChange
public import stacks_project.Chap69.Situation_69_16_1

/-!
# Lemma 69.16.5

In Situation 69.16.1, the absolute canonical morphism
`toSpecA X : extendBase (specULiftZIsTerminal.from S) X ⟶ ofOver (overSpecZ (Spec A))`
is universally injective, where `A = Γ(X, 𝒪_X)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The absolute canonical morphism `p : X ⟶ Spec Γ(X, 𝒪_X)`, obtained by viewing `X`
over `Spec ℤ`, extending the graph `toSpecGamma X`, and projecting from
`S ×_{Spec ℤ} Spec A` onto `Spec A`. Over `Spec ℤ` this is the comparison
`toSpecGamma_specZ` with `GlobalSections.homMk` of `Scheme.ΓSpecIso`. -/
def toSpecA {S : Scheme.{u}} (X : AlgebraicSpace S) :
    extendBase (specULiftZIsTerminal.from S) X ⟶
      ofOver (overSpecZ (Spec (globalSectionsRing X))) :=
  extendBaseMap (specULiftZIsTerminal.from S) (toSpecGamma X) ≫
    (extendBase_ofOver_functorOfPoints (specULiftZIsTerminal.from S)
      (specGammaOver X)).hom ≫
    ofOverMap
      ((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).counit.app
        (overSpecZ (Spec (globalSectionsRing X))))

/-- `toSpecA X` is the extended graph `toSpecGamma X` followed by the counit projection
onto `Spec (globalSectionsRing X)`. -/
theorem toSpecA_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    toSpecA X =
      extendBaseMap (specULiftZIsTerminal.from S) (toSpecGamma X) ≫
        (extendBase_ofOver_functorOfPoints (specULiftZIsTerminal.from S)
          (specGammaOver X)).hom ≫
        ofOverMap
          ((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).counit.app
            (overSpecZ (Spec (globalSectionsRing X)))) :=
  rfl

/-- Lemma 69.16.5: in Situation 69.16.1, the absolute canonical morphism
`toSpecA X` from `X` viewed over `Spec ℤ` to `Spec (globalSectionsRing X)` is
universally injective. -/
@[stacks 07V4]
instance universallyInjective_toSpecA {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] : UniversallyInjective (toSpecA X) :=
  sorry

/-- The morphism `Spec R' ⟶ Spec R` of algebraic spaces over `Spec ℤ`. -/
def specMapSpecZ {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    ofOver (overSpecZ (Spec R')) ⟶ ofOver (overSpecZ (Spec R)) :=
  ofOverMap (Over.homMk (Spec.map φ) (specMap_w φ))

/-- `specMapSpecZ φ` is `ofOverMap` of `Over.homMk` of `Spec.map φ`. -/
theorem specMapSpecZ_eq {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    specMapSpecZ φ = ofOverMap (Over.homMk (Spec.map φ) (specMap_w φ)) :=
  rfl

/-- After base change of `toSpecA X` along a field-valued map
`globalSectionsRing X ⟶ CommRingCat.of K`, the fibre
`Spec K ×_{Spec A} X` has at most one point. -/
theorem subsingleton_points_toSpecAFiber {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u})]
    [HasVanishingH1 X] {K : Type u} [Field K]
    (φ : globalSectionsRing X ⟶ CommRingCat.of K) :
    Subsingleton (Points (pullback (specMapSpecZ φ) (toSpecA X))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
