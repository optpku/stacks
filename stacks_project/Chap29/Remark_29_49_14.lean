/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.RationalMap.PseudoMorphism
import StacksCheckRecall

universe u

/- Remark 29.49.14 (1): a pseudo-partial map from `X` to `Y` consists of a
scheme-theoretically dense open subscheme of `X` and a morphism from it to `Y`. -/
@[stacks 01RX] #check
  (AlgebraicGeometry.Scheme.PseudoPartialMap.mk :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (domain : X.Opens),
      AlgebraicGeometry.schemeTheoreticallyDense domain →
        (domain.toScheme ⟶ Y) → AlgebraicGeometry.Scheme.PseudoPartialMap X Y)

/- Remark 29.49.14 (2): agreement on a scheme-theoretically dense common open
subscheme is an equivalence relation on pseudo-partial maps. -/
@[stacks 01RX] #check
  (AlgebraicGeometry.Scheme.PseudoPartialMap.equivalence_rel :
    ∀ X Y : AlgebraicGeometry.Scheme.{u},
      Equivalence (@AlgebraicGeometry.Scheme.PseudoPartialMap.equiv X Y))

/- Remark 29.49.14 (3): every pseudo-morphism is represented by a pseudo-partial map. -/
@[stacks 01RX] #check
  (AlgebraicGeometry.Scheme.PseudoMorphism.exists_rep :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}}
      (f : AlgebraicGeometry.Scheme.PseudoMorphism X Y),
      ∃ g : AlgebraicGeometry.Scheme.PseudoPartialMap X Y,
        g.toPseudoMorphism = f)

/- Remark 29.49.14 (4): for a reduced source, pseudo-morphisms and ordinary
rational maps are in bijection. -/
@[stacks 01RX] #check
  (AlgebraicGeometry.Scheme.PseudoMorphism.toRationalMap_bijective_of_isReduced :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsReduced X],
      Function.Bijective
        (AlgebraicGeometry.Scheme.PseudoMorphism.toRationalMap :
          AlgebraicGeometry.Scheme.PseudoMorphism X Y →
            AlgebraicGeometry.Scheme.RationalMap X Y))
