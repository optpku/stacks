module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.LocalRing
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.PointIntersection
public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.Ideal

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/-- The strict transform of an integral one-dimensional closed subscheme regular at a closed
blowup center maps isomorphically to the original subscheme. -/
theorem strictTransformFst_isIso_of_regularStalk
    {X X' : Scheme.{u}} [IsLocallyNoetherian X] (Y : X.IdealSheafData)
    [IsIntegral Y.subscheme] (p : X) (hp : p ∈ closedPoints X)
    (hpY : p ∈ Y.support) (hYdim : topologicalKrullDim Y.subscheme = 1)
    [IsRegularLocalRing (Y.subschemeLocalRingAt p hpY)]
    (b : X' ⟶ X) [IsBlowup b (Scheme.PointClosure.reducedStructure p).ideal] :
    IsIso (AlgebraicGeometry.strictTransformFst b
      ((Scheme.PointClosure.reducedStructure p).ideal.comap b) Y.subschemeι) := sorry

/-- The strict transform of an integral curve regular at the closed blowup center meets the
exceptional fibre in one closed point with finite intersection multiplicity one. -/
theorem exists_strictTransform_inter_exceptional
    {X X' : Scheme.{u}} [IsLocallyNoetherian X] (Y : X.IdealSheafData)
    [IsIntegral Y.subscheme] (p : X) (hp : p ∈ closedPoints X)
    (hpY : p ∈ Y.support) (hYdim : topologicalKrullDim Y.subscheme = 1)
    [IsRegularLocalRing (Y.subschemeLocalRingAt p hpY)]
    (b : X' ⟶ X) [IsBlowup b (Scheme.PointClosure.reducedStructure p).ideal] :
    ∃ q : X', q ∈ closedPoints X' ∧
      ((strictTransformIdeal (Scheme.PointClosure.reducedStructure p).ideal b Y).support :
          Set X') ∩
          (((Scheme.PointClosure.reducedStructure p).ideal.comap b).support : Set X') = {q} ∧
        ∃ hfinite :
            (strictTransformIdeal (Scheme.PointClosure.reducedStructure p).ideal b Y).pointIntersectionMultiplicity
                ((Scheme.PointClosure.reducedStructure p).ideal.comap b) q ≠ ⊤,
          (strictTransformIdeal (Scheme.PointClosure.reducedStructure p).ideal b Y).pointIntersectionMultiplicityNat
              ((Scheme.PointClosure.reducedStructure p).ideal.comap b) q hfinite = 1 := sorry

/-- At a closed point on the exceptional fibre and both strict transforms, blowing up a
regular integral curve strictly decreases its finite intersection multiplicity with a closed
subscheme not containing the curve's generic point. -/
theorem strictTransform_pointIntersectionMultiplicity_lt
    {X X' : Scheme.{u}} [IsLocallyNoetherian X] (Y Z : X.IdealSheafData)
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
      (Scheme.PointClosure.reducedStructure p).ideal b Z).support) :
    ∃ hfiniteStrict :
        (strictTransformIdeal (Scheme.PointClosure.reducedStructure p).ideal b Y).pointIntersectionMultiplicity
            (strictTransformIdeal (Scheme.PointClosure.reducedStructure p).ideal b Z) q ≠ ⊤,
      ∃ hfiniteOriginal : Y.pointIntersectionMultiplicity Z p ≠ ⊤,
        (strictTransformIdeal (Scheme.PointClosure.reducedStructure p).ideal b Y).pointIntersectionMultiplicityNat
            (strictTransformIdeal (Scheme.PointClosure.reducedStructure p).ideal b Z) q
              hfiniteStrict <
          Y.pointIntersectionMultiplicityNat Z p hfiniteOriginal := sorry

end AlgebraicGeometry.IsBlowup
