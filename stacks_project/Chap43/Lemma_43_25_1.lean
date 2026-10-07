module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveLineFiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 43.25.1: if an integral `(s + 1)`-dimensional subvariety `W` of
`X × ℙ¹` dominates `ℙ¹`, then the intersections of an `r`-dimensional
subvariety `V` with the degree-`r` cycles of two fibers of `W` are rationally
equivalent whenever both intersections are proper. -/
@[stacks 0B60] #check
  (AlgebraicGeometry.ProjectiveLineFiber.subvarietyIntersections_rationallyEquivalent :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : AlgebraicGeometry.SchemeOverField k) [AlgebraicGeometry.Variety X]
      [AlgebraicGeometry.Scheme.Regular X.left]
      (r s : ℕ) (V : X.left.IdealSheafData)
      [AlgebraicGeometry.Variety (CategoryTheory.Over.mk (V.subschemeι ≫ X.hom))]
      (hVdim : AlgebraicGeometry.SchemeOverField.dimension
        (CategoryTheory.Over.mk (V.subschemeι ≫ X.hom)) = r)
      (W : (X ⨯ CategoryTheory.Over.mk
        (AlgebraicGeometry.ProjectiveLine.toSpec k)).left.IdealSheafData)
      [AlgebraicGeometry.Variety (CategoryTheory.Over.mk
        (W.subschemeι ≫ (X ⨯ CategoryTheory.Over.mk
          (AlgebraicGeometry.ProjectiveLine.toSpec k)).hom))]
      (hWdim : AlgebraicGeometry.SchemeOverField.dimension (CategoryTheory.Over.mk
        (W.subschemeι ≫ (X ⨯ CategoryTheory.Over.mk
          (AlgebraicGeometry.ProjectiveLine.toSpec k)).hom)) = s + 1)
      [AlgebraicGeometry.IsDominant
        (W.subschemeι ≫
          (CategoryTheory.Limits.prod.snd :
            X ⨯ CategoryTheory.Over.mk (AlgebraicGeometry.ProjectiveLine.toSpec k) ⟶
              CategoryTheory.Over.mk
                (AlgebraicGeometry.ProjectiveLine.toSpec k)).left)]
      (a b : AlgebraicGeometry.ProjectiveLine.scheme k)
      (ha : a ∈ closedPoints
        (AlgebraicGeometry.ProjectiveLine.scheme k))
      (hb : b ∈ closedPoints
        (AlgebraicGeometry.ProjectiveLine.scheme k))
      (hproperA : TopologicalSpace.Closeds.IntersectProperly V.support
        (AlgebraicGeometry.ProjectiveLineFiber.image X W a).support)
      (hproperB : TopologicalSpace.Closeds.IntersectProperly V.support
        (AlgebraicGeometry.ProjectiveLineFiber.image X W b).support),
      AlgebraicGeometry.RationalEquivalence.RationallyEquivalent
        (X.hom.relativeDimensionFunction (fun _ ↦ 0))
        ((r : ℤ) + (r : ℤ) - (X.dimension : ℤ))
        (AlgebraicGeometry.CycleGroup.intersection X (r : ℤ) (r : ℤ)
          (V.associatedCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) (r : ℤ))
          ((AlgebraicGeometry.ProjectiveLineFiber.image X W a).associatedCycle
            (X.hom.relativeDimensionFunction (fun _ ↦ 0)) (r : ℤ))
          (AlgebraicGeometry.ProjectiveLineFiber.fiberAssociatedCycles_intersectProperly
            X r s V hVdim W hWdim a ha hproperA))
        (AlgebraicGeometry.CycleGroup.intersection X (r : ℤ) (r : ℤ)
          (V.associatedCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) (r : ℤ))
          ((AlgebraicGeometry.ProjectiveLineFiber.image X W b).associatedCycle
            (X.hom.relativeDimensionFunction (fun _ ↦ 0)) (r : ℤ))
          (AlgebraicGeometry.ProjectiveLineFiber.fiberAssociatedCycles_intersectProperly
            X r s V hVdim W hWdim b hb hproperB)))
