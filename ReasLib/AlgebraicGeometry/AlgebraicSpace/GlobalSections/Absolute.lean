/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase

/-!
# Absolute spectrum morphisms of algebraic spaces

The canonical morphism to the spectrum of global sections and the morphisms
between affine algebraic spaces induced by ring maps, all viewed over `Spec ℤ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The absolute canonical morphism `X ⟶ Spec Γ(X, 𝒪_X)`, obtained by extending
the graph `toSpecGamma X` to `Spec ℤ` and projecting onto the spectrum. -/
def toSpecA {S : Scheme.{u}} (X : AlgebraicSpace S) :
    extendBase (specULiftZIsTerminal.from S) X ⟶
      ofOver (overSpecZ (Spec (globalSectionsRing X))) :=
  NatTrans.vcomp
    (extendBasePresheafMap (specULiftZIsTerminal.from S) (toSpecGamma X))
    (NatTrans.vcomp
      (extendBasePresheafYonedaIso (specULiftZIsTerminal.from S) (specGammaOver X)).hom
      (ofOverMap
        ((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).counit.app
          (overSpecZ (Spec (globalSectionsRing X))))))

/-- `toSpecA X` is the extended graph `toSpecGamma X` followed by the counit
projection onto `Spec (globalSectionsRing X)`. -/
theorem toSpecA_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    toSpecA X =
      NatTrans.vcomp
        (extendBasePresheafMap (specULiftZIsTerminal.from S) (toSpecGamma X))
        (NatTrans.vcomp
          (extendBasePresheafYonedaIso (specULiftZIsTerminal.from S) (specGammaOver X)).hom
          (ofOverMap
            ((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).counit.app
              (overSpecZ (Spec (globalSectionsRing X)))))) :=
  rfl

/-- The morphism `Spec R' ⟶ Spec R` of algebraic spaces over `Spec ℤ` induced
by a ring map `R ⟶ R'`. -/
def specMapSpecZ {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    ofOver (overSpecZ (Spec R')) ⟶ ofOver (overSpecZ (Spec R)) :=
  ofOverMap (Over.homMk (Spec.map φ) (specMap_w φ))

/-- `specMapSpecZ φ` is `ofOverMap` of `Over.homMk` of `Spec.map φ`. -/
theorem specMapSpecZ_eq {R R' : CommRingCat.{u}} (φ : R ⟶ R') :
    specMapSpecZ φ = ofOverMap (Over.homMk (Spec.map φ) (specMap_w φ)) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
