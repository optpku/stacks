/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveLineFiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 43.17.1 (1): if an integral `(n + 1)`-dimensional closed subvariety `W`
of `X × ℙ¹` meets `X × {a}` properly, then the degree-`n` cycle of the
scheme-theoretic fiber equals the intersection cycle `W · (X × {a})`. -/
@[stacks 0B07] #check
  (AlgebraicGeometry.ProjectiveLineFiber.associatedCycle_fiber_eq_intersection :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
      (n : ℤ) (hn : 0 ≤ n) (a : ProjectiveLine.scheme k)
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
          (X.dimension : ℤ) (ProjectiveLineFiber.cycle X a))),
      @Scheme.IdealSheafData.associatedCycle
          (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
          (LocallyOfFiniteType.isLocallyNoetherian
            (X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
          (W ⊔ ProjectiveLineFiber.ideal X a)
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0)) n =
        ProjectiveLineFiber.intersectionCycle X n
          (@Scheme.IdealSheafData.associatedCycle
            (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
            (LocallyOfFiniteType.isLocallyNoetherian
              (X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
            W ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
              (fun _ ↦ 0)) (n + 1)) a ha hproper)

/- The second clause identifies the fiber cycle on `X` with the pushforward of the
intersection cycle along the first projection. -/
#check
  (AlgebraicGeometry.ProjectiveLineFiber.associatedCycle_fiberImage_eq_map_intersection :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
      (n : ℤ) (hn : 0 ≤ n) (a : ProjectiveLine.scheme k)
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
          (X.dimension : ℤ) (ProjectiveLineFiber.cycle X a))),
      @Scheme.IdealSheafData.associatedCycle X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (ProjectiveLineFiber.image X W a)
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n =
        @CycleGroup.mapHom _ _
          (prod.fst : X ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ X).left
          ({ isCompact_preimage := fun _ _ ↦
              (@Scheme.Hom.isProperMap _ _ _
                (@SchemeOverField.prodFstIsProper k _ X
                  (Over.mk (ProjectiveLine.toSpec k))
                  (ProjectiveSpace.toSpec_isProper k 1)).toUniversallyClosed).isCompact_preimage } :
            QuasiCompact (prod.fst : X ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ X).left)
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0))
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n
          (ProjectiveLineFiber.intersectionCycle X n
            (@Scheme.IdealSheafData.associatedCycle
              (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
              (LocallyOfFiniteType.isLocallyNoetherian
                (X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
              W ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
                (fun _ ↦ 0)) (n + 1)) a ha hproper))

/- The third clause says that the projected difference at two distinct closed fibers is
rationally trivial. -/
#check
  (AlgebraicGeometry.ProjectiveLineFiber.projectedDifference_isRationallyTrivial :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
      (n : ℤ) (hn : 0 ≤ n) (a b : ProjectiveLine.scheme k)
      (ha : a ∈ closedPoints (ProjectiveLine.scheme k))
      (hb : b ∈ closedPoints (ProjectiveLine.scheme k)) (hab : a ≠ b)
      (alpha : CycleGroup (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
        ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
          (fun _ ↦ 0)) (n + 1))
      (hproperA : AlgebraicCycle.IntersectProperly
        (CycleGroup.toAlgebraicCycle
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
          (n + 1) alpha)
        (CycleGroup.toAlgebraicCycle
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
          (X.dimension : ℤ) (ProjectiveLineFiber.cycle X a)))
      (hproperB : AlgebraicCycle.IntersectProperly
        (CycleGroup.toAlgebraicCycle
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
          (n + 1) alpha)
        (CycleGroup.toAlgebraicCycle
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
          (X.dimension : ℤ) (ProjectiveLineFiber.cycle X b))),
      @RationalEquivalence.IsRationallyTrivial X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n
        (ProjectiveLineFiber.projectedDifference X n alpha a b ha hb hproperA hproperB))

/- The fourth clause realizes every rationally trivial cycle as a projected difference at
the fixed distinct closed fibers. -/
#check
  (AlgebraicGeometry.ProjectiveLineFiber.exists_projectedDifference_eq_of_isRationallyTrivial :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
      (n : ℤ) (hn : 0 ≤ n) (a b : ProjectiveLine.scheme k)
      (ha : a ∈ closedPoints (ProjectiveLine.scheme k))
      (hb : b ∈ closedPoints (ProjectiveLine.scheme k)) (hab : a ≠ b)
      (beta : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) n)
      (hbeta : @RationalEquivalence.IsRationallyTrivial X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance n beta),
      ∃ (alpha : CycleGroup (X ⨯ Over.mk (ProjectiveLine.toSpec k)).left
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0)) (n + 1))
        (hproperA : AlgebraicCycle.IntersectProperly
          (CycleGroup.toAlgebraicCycle
            ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
              (fun _ ↦ 0)) (n + 1) alpha)
          (CycleGroup.toAlgebraicCycle
            ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
              (fun _ ↦ 0)) (X.dimension : ℤ) (ProjectiveLineFiber.cycle X a)))
        (hproperB : AlgebraicCycle.IntersectProperly
          (CycleGroup.toAlgebraicCycle
            ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
              (fun _ ↦ 0)) (n + 1) alpha)
          (CycleGroup.toAlgebraicCycle
            ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
              (fun _ ↦ 0)) (X.dimension : ℤ) (ProjectiveLineFiber.cycle X b))),
        beta = ProjectiveLineFiber.projectedDifference
          X n alpha a b ha hb hproperA hproperB)
