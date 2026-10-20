/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Intersection
public import ReasLib.AlgebraicGeometry.ChowGroup.Pushforward
public import ReasLib.AlgebraicGeometry.CycleGroup.Intersection
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.FunctionField
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Variety
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Proper
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regular
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionMultiplicity.Principal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Product.Proper

/-!
# Cycles from fibers over the projective line

This file defines the cycle of a fiber over a closed point of the projective line, its
intersection with a cycle on the product, and the resulting pushforward to the other factor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLineFiber

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The projective-line fiber `X × {a}` as a closed subscheme of `X × ℙ¹`. -/
noncomputable def ideal (X : SchemeOverField k) (a : ProjectiveLine.scheme k) :
    (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left.IdealSheafData :=
  (Scheme.PointClosure.reducedStructure a).ideal.comap
    ((prod.snd : X ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶
      Over.mk (ProjectiveLine.toSpec k)).left)

/-- The cycle of `X × {a}`, placed in the dimension of `X`. -/
noncomputable def cycle (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
    (a : ProjectiveLine.scheme k) :
    CycleGroup (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
      ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
      (X.dimension : ℤ) :=
  @Scheme.IdealSheafData.associatedCycle
    (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
    (@Scheme.instIsLocallyNoetherianOfRegular
      ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).left)
      (@SchemeOverField.regularProdOfRegular k _ _ X
        (Over.mk (ProjectiveLine.toSpec k)) _ _ _
        (ProjectiveSpace.regularScheme k 1)))
    (ideal X a)
    ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
    (X.dimension : ℤ)

/-- The restriction of a closed subscheme of `X × ℙ¹` to the fiber at `a`, followed by
the first projection to `X`. -/
noncomputable def toX (X : SchemeOverField k)
    (W : (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left.IdealSheafData)
    (a : ProjectiveLine.scheme k) : (W ⊔ ideal X a).subscheme ⟶ X.left :=
  (W ⊔ ideal X a).subschemeι ≫
    (prod.fst : X ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ X).left

/-- The fiber of `W` at `a`, viewed by its scheme-theoretic image as a closed subscheme
of `X`. -/
noncomputable def image (X : SchemeOverField k)
    (W : (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left.IdealSheafData)
    (a : ProjectiveLine.scheme k) : X.left.IdealSheafData :=
  (toX X W a).ker

/-- Intersecting a `(n + 1)`-cycle on `X × ℙ¹` properly with the fiber over a closed
point produces a degree-`n` cycle. -/
theorem intersection_mem_dimensionSubgroup (X : SchemeOverField k) [Variety X]
    [Scheme.Regular X.left] (n : ℤ)
    (alpha : CycleGroup (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
      ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
      (n + 1))
    (a : ProjectiveLine.scheme k) (ha : a ∈ closedPoints (ProjectiveLine.scheme k))
    (hproper : AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (n + 1) alpha)
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (X.dimension : ℤ) (cycle X a))) :
    @AlgebraicCycle.intersection
      (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
      (@SchemeOverField.regularProdOfRegular k _ _ X
        (Over.mk (ProjectiveLine.toSpec k)) _ _ _
        (ProjectiveSpace.regularScheme k 1))
        (CycleGroup.toAlgebraicCycle
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
          (n + 1) alpha)
        (CycleGroup.toAlgebraicCycle
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
          (X.dimension : ℤ) (cycle X a)) hproper ∈
      AlgebraicCycle.dimensionSubgroup
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0)) n :=
  sorry

/-- The graded intersection of a cycle on `X × ℙ¹` with the fiber over a closed point. -/
noncomputable def intersectionCycle (X : SchemeOverField k) [Variety X]
    [Scheme.Regular X.left] (n : ℤ)
    (alpha : CycleGroup (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
      ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
      (n + 1))
    (a : ProjectiveLine.scheme k) (ha : a ∈ closedPoints (ProjectiveLine.scheme k))
    (hproper : AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (n + 1) alpha)
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (X.dimension : ℤ) (cycle X a))) :
    CycleGroup (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
      ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0)) n :=
  ⟨@AlgebraicCycle.intersection
      (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
      (@SchemeOverField.regularProdOfRegular k _ _ X
        (Over.mk (ProjectiveLine.toSpec k)) _ _ _
        (ProjectiveSpace.regularScheme k 1))
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (n + 1) alpha)
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (X.dimension : ℤ) (cycle X a)) hproper,
    intersection_mem_dimensionSubgroup X n alpha a ha hproper⟩

/-- The pushforward to `X` of the difference between the intersections with two
projective-line fibers. -/
noncomputable def projectedDifference (X : SchemeOverField k) [Variety X]
    [Scheme.Regular X.left] (n : ℤ)
    (alpha : CycleGroup (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
      ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
      (n + 1))
    (a b : ProjectiveLine.scheme k)
    (ha : a ∈ closedPoints (ProjectiveLine.scheme k))
    (hb : b ∈ closedPoints (ProjectiveLine.scheme k))
    (hproperA : AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (n + 1) alpha)
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (X.dimension : ℤ) (cycle X a)))
    (hproperB : AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (n + 1) alpha)
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (X.dimension : ℤ) (cycle X b))) :
    CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n :=
  @CycleGroup.mapHom _ _
    (prod.fst : X ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ X).left
    ({ isCompact_preimage := fun _ _ ↦
        (@Scheme.Hom.isProperMap _ _ _
          (@SchemeOverField.prodFstIsProper k _ X (Over.mk (ProjectiveLine.toSpec k))
            (ProjectiveSpace.toSpec_isProper k 1)).toUniversallyClosed).isCompact_preimage } :
      QuasiCompact (prod.fst : X ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ X).left)
    ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
    (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n
    (intersectionCycle X n alpha a ha hproperA -
      intersectionCycle X n alpha b hb hproperB)

/-- For a proper fiber intersection, the associated cycle of the scheme-theoretic fiber
equals its intersection cycle. -/
theorem associatedCycle_fiber_eq_intersection (X : SchemeOverField k) [Variety X]
    [Scheme.Regular X.left] (n : ℤ) (hn : 0 ≤ n)
    (a : ProjectiveLine.scheme k)
    (ha : a ∈ closedPoints (ProjectiveLine.scheme k))
    (W : (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left.IdealSheafData)
    [IsIntegral W.subscheme]
    (hW : (X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.closedSubschemeDeltaDimension
      (fun _ ↦ 0) W = ((n + 1 : ℤ) : EInt))
    (hproper : AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (n + 1)
        (@Scheme.IdealSheafData.associatedCycle
          (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
          (LocallyOfFiniteType.isLocallyNoetherian
            (X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
          W ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0)) (n + 1)))
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (X.dimension : ℤ) (cycle X a))) :
    @Scheme.IdealSheafData.associatedCycle
        (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
        (LocallyOfFiniteType.isLocallyNoetherian
          (X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
        (W ⊔ ideal X a)
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0)) n =
      intersectionCycle X n
        (@Scheme.IdealSheafData.associatedCycle
          (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
          (LocallyOfFiniteType.isLocallyNoetherian
            (X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
          W ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0)) (n + 1)) a ha hproper :=
  sorry

/-- For a proper fiber intersection, the associated cycle on `X` is the pushforward of
the intersection cycle along the first projection. -/
theorem associatedCycle_fiberImage_eq_map_intersection (X : SchemeOverField k)
    [Variety X] [Scheme.Regular X.left] (n : ℤ) (hn : 0 ≤ n)
    (a : ProjectiveLine.scheme k)
    (ha : a ∈ closedPoints (ProjectiveLine.scheme k))
    (W : (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left.IdealSheafData)
    [IsIntegral W.subscheme]
    (hW : (X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.closedSubschemeDeltaDimension
      (fun _ ↦ 0) W = ((n + 1 : ℤ) : EInt))
    (hproper : AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (n + 1)
        (@Scheme.IdealSheafData.associatedCycle
          (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
          (LocallyOfFiniteType.isLocallyNoetherian
            (X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
          W ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0)) (n + 1)))
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (X.dimension : ℤ) (cycle X a))) :
    @Scheme.IdealSheafData.associatedCycle X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom) (image X W a)
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n =
      @CycleGroup.mapHom _ _
        (prod.fst : X ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ X).left
        ({ isCompact_preimage := fun _ _ ↦
            (@Scheme.Hom.isProperMap _ _ _
              (@SchemeOverField.prodFstIsProper k _ X (Over.mk (ProjectiveLine.toSpec k))
                (ProjectiveSpace.toSpec_isProper k 1)).toUniversallyClosed).isCompact_preimage } :
          QuasiCompact (prod.fst : X ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ X).left)
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n
        (intersectionCycle X n
          (@Scheme.IdealSheafData.associatedCycle
            (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
            (LocallyOfFiniteType.isLocallyNoetherian
              (X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
            W ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
              (fun _ ↦ 0)) (n + 1)) a ha hproper) :=
  sorry

/-- The pushforward of the difference of proper intersections with two distinct closed
projective-line fibers is rationally trivial. -/
theorem projectedDifference_isRationallyTrivial (X : SchemeOverField k) [Variety X]
    [Scheme.Regular X.left] (n : ℤ) (hn : 0 ≤ n)
    (a b : ProjectiveLine.scheme k)
    (ha : a ∈ closedPoints (ProjectiveLine.scheme k))
    (hb : b ∈ closedPoints (ProjectiveLine.scheme k)) (hab : a ≠ b)
    (alpha : CycleGroup (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
      ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
      (n + 1))
    (hproperA : AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (n + 1) alpha)
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (X.dimension : ℤ) (cycle X a)))
    (hproperB : AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (n + 1) alpha)
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (X.dimension : ℤ) (cycle X b))) :
    @RationalEquivalence.IsRationallyTrivial X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n
      (projectedDifference X n alpha a b ha hb hproperA hproperB) :=
  sorry

/-- Every rationally trivial cycle is the pushforward of a difference of proper
intersections with two fixed distinct closed projective-line fibers. -/
theorem exists_projectedDifference_eq_of_isRationallyTrivial
    (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
    (n : ℤ) (hn : 0 ≤ n) (a b : ProjectiveLine.scheme k)
    (ha : a ∈ closedPoints (ProjectiveLine.scheme k))
    (hb : b ∈ closedPoints (ProjectiveLine.scheme k)) (hab : a ≠ b)
    (beta : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)
    (hbeta : @RationalEquivalence.IsRationallyTrivial X.left
      (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n beta) :
    ∃ (alpha : CycleGroup (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (n + 1))
      (hproperA : AlgebraicCycle.IntersectProperly
        (CycleGroup.toAlgebraicCycle
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
          (n + 1) alpha)
        (CycleGroup.toAlgebraicCycle
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
          (X.dimension : ℤ) (cycle X a)))
      (hproperB : AlgebraicCycle.IntersectProperly
        (CycleGroup.toAlgebraicCycle
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
          (n + 1) alpha)
        (CycleGroup.toAlgebraicCycle
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
          (X.dimension : ℤ) (cycle X b))),
      beta = projectedDifference X n alpha a b ha hb hproperA hproperB :=
  sorry

/-- Proper intersection of an `r`-dimensional subvariety `V` with the fiber at `a` of an
`(s + 1)`-dimensional subvariety `W` dominating `ℙ¹` implies proper intersection of the
`r`-cycle `[V]` with the `s`-cycle `[W_a]_s`. -/
theorem fiberAssociatedCycles_intersectProperly
    (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
    (r s : ℕ) (V : X.left.IdealSheafData)
    [Variety (Over.mk (V.subschemeι ≫ X.hom))]
    (hVdim : SchemeOverField.dimension (Over.mk (V.subschemeι ≫ X.hom)) = r)
    (W : (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left.IdealSheafData)
    [Variety (Over.mk
      (W.subschemeι ≫ (X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom))]
    (hWdim : SchemeOverField.dimension (Over.mk
      (W.subschemeι ≫ (X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)) = s + 1)
    [IsDominant
      (W.subschemeι ≫
        (prod.snd : X ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶
          Over.mk (ProjectiveLine.toSpec k)).left)]
    (a : ProjectiveLine.scheme k)
    (ha : a ∈ closedPoints (ProjectiveLine.scheme k))
    (hproper : Closeds.IntersectProperly V.support (image X W a).support) :
    AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0))
        (r : ℤ) (V.associatedCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) (r : ℤ)))
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0))
        (s : ℤ) ((image X W a).associatedCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) (s : ℤ))) := sorry

/-- If an integral `(s + 1)`-dimensional subvariety `W` of `X × ℙ¹` dominates `ℙ¹`,
then the intersections of an `r`-dimensional subvariety `V` with the `s`-cycles
`[W_a]_s` and `[W_b]_s` of two fibers of `W` are rationally equivalent in degree
`r + s - dim X` whenever both intersections are proper. The printed subscript `[W_a]_r`
in Stacks 0B60 is a typo: its proof invokes Stacks 0B07, which yields `[W_a]_s`. -/
theorem subvarietyIntersections_rationallyEquivalent
    (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
    (r s : ℕ) (V : X.left.IdealSheafData)
    [Variety (Over.mk (V.subschemeι ≫ X.hom))]
    (hVdim : SchemeOverField.dimension (Over.mk (V.subschemeι ≫ X.hom)) = r)
    (W : (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left.IdealSheafData)
    [Variety (Over.mk
      (W.subschemeι ≫ (X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom))]
    (hWdim : SchemeOverField.dimension (Over.mk
      (W.subschemeι ≫ (X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)) = s + 1)
    [IsDominant
      (W.subschemeι ≫
        (prod.snd : X ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶
          Over.mk (ProjectiveLine.toSpec k)).left)]
    (a b : ProjectiveLine.scheme k)
    (ha : a ∈ closedPoints (ProjectiveLine.scheme k))
    (hb : b ∈ closedPoints (ProjectiveLine.scheme k))
    (hproperA : Closeds.IntersectProperly V.support (image X W a).support)
    (hproperB : Closeds.IntersectProperly V.support (image X W b).support) :
    RationalEquivalence.RationallyEquivalent
      (X.hom.relativeDimensionFunction (fun _ ↦ 0))
      ((r : ℤ) + (s : ℤ) - (X.dimension : ℤ))
      (CycleGroup.intersection X (r : ℤ) (s : ℤ)
        (V.associatedCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) (r : ℤ))
        ((image X W a).associatedCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) (s : ℤ))
        (fiberAssociatedCycles_intersectProperly X r s V hVdim W hWdim a ha hproperA))
      (CycleGroup.intersection X (r : ℤ) (s : ℤ)
        (V.associatedCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) (r : ℤ))
        ((image X W b).associatedCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) (s : ℤ))
        (fiberAssociatedCycles_intersectProperly X r s V hVdim W hWdim b hb hproperB)) := sorry

/-- The product of a closed immersion with the identity on the projective line is
quasi-compact. -/
instance instQuasiCompactProdMapProjectiveLine (X P : SchemeOverField k)
    (i : X ⟶ P) [IsClosedImmersion i.left] :
    QuasiCompact (prod.map i (𝟙 (Over.mk (ProjectiveLine.toSpec k)))).left := sorry

/-- The product of regular varieties over an algebraically closed field is regular. -/
instance instRegularProdProjectiveLine (X : SchemeOverField k) [Variety X]
    [Scheme.Regular X.left] :
    Scheme.Regular (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left := sorry

/-- The first projection from a product with the projective line is quasi-compact. -/
instance instQuasiCompactProdFstProjectiveLine (X : SchemeOverField k) :
    QuasiCompact (prod.fst : X ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ X).left := sorry

/-- A proper intersection with a closed immersion remains proper after taking the
zero fiber of a dominant family over the projective line. -/
theorem intersectsProperly_zeroFiber (X P : SchemeOverField k)
    [Variety X] [Variety P] [Scheme.Regular X.left] [Scheme.Regular P.left]
    (i : X ⟶ P) [IsClosedImmersion i.left] (r : ℤ) (hr : 0 ≤ r)
    (C' : (P ⨯ Over.mk (ProjectiveLine.toSpec k)).left.IdealSheafData)
    [IsIntegral C'.subscheme] (C : P.left.IdealSheafData)
    (hC' : (P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.closedSubschemeDeltaDimension
      (fun _ ↦ 0) C' = ((r + 1 : ℤ) : EInt))
    (hC : P.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) C = (r : EInt))
    [IsDominant
      (C'.subschemeι ≫
        (prod.snd : P ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶
          Over.mk (ProjectiveLine.toSpec k)).left)]
    (hCfiber : C = image P C' (ProjectiveLine.zeroPoint k))
    (hCproper : AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle (P.hom.relativeDimensionFunction (fun _ ↦ 0)) r
        (@Scheme.IdealSheafData.associatedCycle P.left
          (LocallyOfFiniteType.isLocallyNoetherian P.hom) C
          (P.hom.relativeDimensionFunction (fun _ ↦ 0)) r))
      (CycleGroup.toAlgebraicCycle (P.hom.relativeDimensionFunction (fun _ ↦ 0))
        (X.dimension : ℤ)
        (@Scheme.IdealSheafData.associatedCycle P.left
          (LocallyOfFiniteType.isLocallyNoetherian P.hom) i.left.ker
          (P.hom.relativeDimensionFunction (fun _ ↦ 0)) (X.dimension : ℤ))))
    (hC'proper : AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle
        ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (r + 1)
        (@Scheme.IdealSheafData.associatedCycle
          (P ⨯ Over.mk (ProjectiveLine.toSpec k)).left
          (LocallyOfFiniteType.isLocallyNoetherian
            (P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
          C' ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0)) (r + 1)))
      (CycleGroup.toAlgebraicCycle
        ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).dimension : ℤ)
        (@Scheme.IdealSheafData.associatedCycle
          (P ⨯ Over.mk (ProjectiveLine.toSpec k)).left
          (LocallyOfFiniteType.isLocallyNoetherian
            (P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
          (comap i.left.ker
            (prod.fst : P ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ P).left)
          ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0))
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).dimension : ℤ))))
    (beta : AlgebraicCycle (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left ℤ)
    (hBetaView : AlgebraicCycle.map
      (prod.map i (𝟙 (Over.mk (ProjectiveLine.toSpec k)))).left
      ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
      ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
      beta =
        AlgebraicCycle.intersection
          (CycleGroup.toAlgebraicCycle
            ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
              (fun _ ↦ 0))
            (r + 1)
            (@Scheme.IdealSheafData.associatedCycle
              (P ⨯ Over.mk (ProjectiveLine.toSpec k)).left
              (LocallyOfFiniteType.isLocallyNoetherian
                (P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
              C' ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
                (fun _ ↦ 0)) (r + 1)))
          (CycleGroup.toAlgebraicCycle
            ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
              (fun _ ↦ 0))
            ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).dimension : ℤ)
            (@Scheme.IdealSheafData.associatedCycle
              (P ⨯ Over.mk (ProjectiveLine.toSpec k)).left
              (LocallyOfFiniteType.isLocallyNoetherian
                (P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
              (comap i.left.ker
                (prod.fst : P ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ P).left)
              ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
                (fun _ ↦ 0))
              ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).dimension : ℤ))) hC'proper) :
    AlgebraicCycle.IntersectProperly beta
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (X.dimension : ℤ) (cycle X (ProjectiveLine.zeroPoint k))) := sorry

/-- Proper intersection with a closed immersion commutes with taking the zero fiber
and pushing forward along the first projection. -/
theorem intersection_eq_map_zeroFiber (X P : SchemeOverField k)
    [Variety X] [Variety P] [Scheme.Regular X.left] [Scheme.Regular P.left]
    (i : X ⟶ P) [IsClosedImmersion i.left] (r : ℤ) (hr : 0 ≤ r)
    (C' : (P ⨯ Over.mk (ProjectiveLine.toSpec k)).left.IdealSheafData)
    [IsIntegral C'.subscheme] (C : P.left.IdealSheafData)
    (hC' : (P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.closedSubschemeDeltaDimension
      (fun _ ↦ 0) C' = ((r + 1 : ℤ) : EInt))
    (hC : P.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) C = (r : EInt))
    [IsDominant
      (C'.subschemeι ≫
        (prod.snd : P ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶
          Over.mk (ProjectiveLine.toSpec k)).left)]
    (hCfiber : C = image P C' (ProjectiveLine.zeroPoint k))
    (hCproper : AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle (P.hom.relativeDimensionFunction (fun _ ↦ 0)) r
        (@Scheme.IdealSheafData.associatedCycle P.left
          (LocallyOfFiniteType.isLocallyNoetherian P.hom) C
          (P.hom.relativeDimensionFunction (fun _ ↦ 0)) r))
      (CycleGroup.toAlgebraicCycle (P.hom.relativeDimensionFunction (fun _ ↦ 0))
        (X.dimension : ℤ)
        (@Scheme.IdealSheafData.associatedCycle P.left
          (LocallyOfFiniteType.isLocallyNoetherian P.hom) i.left.ker
          (P.hom.relativeDimensionFunction (fun _ ↦ 0)) (X.dimension : ℤ))))
    (hC'proper : AlgebraicCycle.IntersectProperly
      (CycleGroup.toAlgebraicCycle
        ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        (r + 1)
        (@Scheme.IdealSheafData.associatedCycle
          (P ⨯ Over.mk (ProjectiveLine.toSpec k)).left
          (LocallyOfFiniteType.isLocallyNoetherian
            (P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
          C' ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0)) (r + 1)))
      (CycleGroup.toAlgebraicCycle
        ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).dimension : ℤ)
        (@Scheme.IdealSheafData.associatedCycle
          (P ⨯ Over.mk (ProjectiveLine.toSpec k)).left
          (LocallyOfFiniteType.isLocallyNoetherian
            (P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
          (comap i.left.ker
            (prod.fst : P ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ P).left)
          ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0))
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).dimension : ℤ))))
    (alpha : AlgebraicCycle X.left ℤ)
    (hAlphaView : AlgebraicCycle.map i.left
      (X.hom.relativeDimensionFunction (fun _ ↦ 0))
      (P.hom.relativeDimensionFunction (fun _ ↦ 0)) alpha =
        AlgebraicCycle.intersection
          (CycleGroup.toAlgebraicCycle (P.hom.relativeDimensionFunction (fun _ ↦ 0)) r
            (@Scheme.IdealSheafData.associatedCycle P.left
              (LocallyOfFiniteType.isLocallyNoetherian P.hom) C
              (P.hom.relativeDimensionFunction (fun _ ↦ 0)) r))
          (CycleGroup.toAlgebraicCycle (P.hom.relativeDimensionFunction (fun _ ↦ 0))
            (X.dimension : ℤ)
            (@Scheme.IdealSheafData.associatedCycle P.left
              (LocallyOfFiniteType.isLocallyNoetherian P.hom) i.left.ker
              (P.hom.relativeDimensionFunction (fun _ ↦ 0)) (X.dimension : ℤ))) hCproper)
    (beta : AlgebraicCycle (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left ℤ)
    (hBetaView : AlgebraicCycle.map
      (prod.map i (𝟙 (Over.mk (ProjectiveLine.toSpec k)))).left
      ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
      ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
      beta =
        AlgebraicCycle.intersection
          (CycleGroup.toAlgebraicCycle
            ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
              (fun _ ↦ 0))
            (r + 1)
            (@Scheme.IdealSheafData.associatedCycle
              (P ⨯ Over.mk (ProjectiveLine.toSpec k)).left
              (LocallyOfFiniteType.isLocallyNoetherian
                (P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
              C' ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
                (fun _ ↦ 0)) (r + 1)))
          (CycleGroup.toAlgebraicCycle
            ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
              (fun _ ↦ 0))
            ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).dimension : ℤ)
            (@Scheme.IdealSheafData.associatedCycle
              (P ⨯ Over.mk (ProjectiveLine.toSpec k)).left
              (LocallyOfFiniteType.isLocallyNoetherian
                (P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
              (comap i.left.ker
                (prod.fst : P ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ P).left)
              ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
                (fun _ ↦ 0))
              ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).dimension : ℤ))) hC'proper) :
    alpha = AlgebraicCycle.map
      (prod.fst : X ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ X).left
      ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
      (X.hom.relativeDimensionFunction (fun _ ↦ 0))
      (AlgebraicCycle.intersection beta
        (CycleGroup.toAlgebraicCycle
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0))
          (X.dimension : ℤ) (cycle X (ProjectiveLine.zeroPoint k)))
        (intersectsProperly_zeroFiber X P i r hr C' C hC' hC hCfiber
          hCproper hC'proper beta hBetaView)) := sorry

end AlgebraicGeometry.ProjectiveLineFiber
