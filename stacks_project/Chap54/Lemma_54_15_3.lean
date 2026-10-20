/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Blowup.RegularCurve
import StacksCheckRecall

open CategoryTheory TopologicalSpace AlgebraicGeometry AlgebraicGeometry.IsBlowup

universe u

/- Lemma 54.15.3 (1): the strict transform of an integral curve that is regular at the closed
blowup center maps isomorphically to the original curve. -/
@[stacks 0BI7] #check
  (AlgebraicGeometry.IsBlowup.strictTransformFst_isIso_of_regularStalk :
    ∀ {X X' : Scheme.{u}} [IsLocallyNoetherian X] (Y : X.IdealSheafData)
    [IsIntegral Y.subscheme] (p : X) (hp : p ∈ closedPoints X)
    (hpY : p ∈ Y.support) (hYdim : topologicalKrullDim Y.subscheme = 1)
    [IsRegularLocalRing (Y.subschemeLocalRingAt p hpY)]
    (b : X' ⟶ X) [IsBlowup b (Scheme.PointClosure.reducedStructure p).ideal],
    IsIso (AlgebraicGeometry.strictTransformFst b
      ((Scheme.PointClosure.reducedStructure p).ideal.comap b) Y.subschemeι))

/- Lemma 54.15.3 (2): the strict transform of an integral curve regular at the closed blowup
center meets the exceptional fibre in one closed point, where the finite natural-valued
intersection multiplicity is one. -/
@[stacks 0BI7] #check
  (AlgebraicGeometry.IsBlowup.exists_strictTransform_inter_exceptional :
    ∀ {X X' : Scheme.{u}} [IsLocallyNoetherian X] (Y : X.IdealSheafData)
    [IsIntegral Y.subscheme] (p : X) (hp : p ∈ closedPoints X)
    (hpY : p ∈ Y.support) (hYdim : topologicalKrullDim Y.subscheme = 1)
    [IsRegularLocalRing (Y.subschemeLocalRingAt p hpY)]
    (b : X' ⟶ X) [IsBlowup b (Scheme.PointClosure.reducedStructure p).ideal],
    ∃ q : X', q ∈ closedPoints X' ∧
      ((strictTransformIdeal (Scheme.PointClosure.reducedStructure p).ideal b Y).support :
          Set X') ∩
          (((Scheme.PointClosure.reducedStructure p).ideal.comap b).support : Set X') = {q} ∧
        ∃ hfinite :
            (strictTransformIdeal (Scheme.PointClosure.reducedStructure p).ideal b Y).pointIntersectionMultiplicity
                ((Scheme.PointClosure.reducedStructure p).ideal.comap b) q ≠ ⊤,
          (strictTransformIdeal (Scheme.PointClosure.reducedStructure p).ideal b Y).pointIntersectionMultiplicityNat
              ((Scheme.PointClosure.reducedStructure p).ideal.comap b) q hfinite = 1)

/- Lemma 54.15.3 (3): if the exceptional intersection point also lies on the strict transform
of `Z`, then the finite natural-valued pointwise intersection multiplicity with `Y` strictly
decreases after blowing up. -/
@[stacks 0BI7] #check
  (AlgebraicGeometry.IsBlowup.strictTransform_pointIntersectionMultiplicity_lt :
    ∀ {X X' : Scheme.{u}} [IsLocallyNoetherian X] (Y Z : X.IdealSheafData)
    [IsIntegral Y.subscheme] (p : X) (hp : p ∈ closedPoints X)
    (hpY : p ∈ Y.support) (hpZ : p ∈ Z.support)
    (hYdim : topologicalKrullDim Y.subscheme = 1)
    (hgeneric : Y.subschemeι (_root_.genericPoint Y.subscheme) ∉ Z.support)
    [IsRegularLocalRing (Y.subschemeLocalRingAt p hpY)]
    (b : X' ⟶ X) [IsBlowup b (Scheme.PointClosure.reducedStructure p).ideal]
    (q : X') (hq : q ∈ closedPoints X')
    (hqY : q ∈ (strictTransformIdeal
      (Scheme.PointClosure.reducedStructure p).ideal b Y).support)
    (hqE : q ∈ ((Scheme.PointClosure.reducedStructure p).ideal.comap b).support)
    (hqZ : q ∈ (strictTransformIdeal
      (Scheme.PointClosure.reducedStructure p).ideal b Z).support),
    ∃ hfiniteStrict :
        (strictTransformIdeal (Scheme.PointClosure.reducedStructure p).ideal b Y).pointIntersectionMultiplicity
            (strictTransformIdeal (Scheme.PointClosure.reducedStructure p).ideal b Z) q ≠ ⊤,
      ∃ hfiniteOriginal : Y.pointIntersectionMultiplicity Z p ≠ ⊤,
        (strictTransformIdeal (Scheme.PointClosure.reducedStructure p).ideal b Y).pointIntersectionMultiplicityNat
            (strictTransformIdeal (Scheme.PointClosure.reducedStructure p).ideal b Z) q
              hfiniteStrict <
          Y.pointIntersectionMultiplicityNat Z p hfiniteOriginal)
