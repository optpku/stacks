/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveLineFiber
import StacksCheckRecall

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData
open scoped AlgebraicGeometry

/- Lemma 43.22.2: proper intersection with a closed immersion commutes with taking the zero fiber of a dominant family over the projective line and pushing it forward to X. -/
@[stacks 0B1M] #check (AlgebraicGeometry.ProjectiveLineFiber.intersection_eq_map_zeroFiber :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X P : SchemeOverField k) [Variety X] [Variety P]
    [Scheme.Regular X.left] [Scheme.Regular P.left]
    (i : X ⟶ P) [IsClosedImmersion i.left] (r : ℤ) (hr : 0 ≤ r)
    (C' : (P ⨯ Over.mk (ProjectiveLine.toSpec k)).left.IdealSheafData)
    [IsIntegral C'.subscheme] (C : P.left.IdealSheafData)
    (hC' : (P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.closedSubschemeDeltaDimension
      (fun _ ↦ 0) C' = ((r + 1 : ℤ) : EInt))
    (hC : P.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) C = (r : EInt))
    [IsDominant (C'.subschemeι ≫
      (prod.snd : P ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶
        Over.mk (ProjectiveLine.toSpec k)).left)]
    (hCfiber : C = ProjectiveLineFiber.image P C' (ProjectiveLine.zeroPoint k))
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
        ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
          (fun _ ↦ 0)) (r + 1)
        (@Scheme.IdealSheafData.associatedCycle
          (P ⨯ Over.mk (ProjectiveLine.toSpec k)).left
          (LocallyOfFiniteType.isLocallyNoetherian
            (P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom) C'
          ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0)) (r + 1)))
      (CycleGroup.toAlgebraicCycle
        ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
          (fun _ ↦ 0)) ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).dimension : ℤ)
        (@Scheme.IdealSheafData.associatedCycle
          (P ⨯ Over.mk (ProjectiveLine.toSpec k)).left
          (LocallyOfFiniteType.isLocallyNoetherian
            (P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
          (comap i.left.ker
            (prod.fst : P ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ P).left)
          ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0)) ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).dimension : ℤ))))
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
      ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
        (fun _ ↦ 0))
      ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
        (fun _ ↦ 0)) beta =
      AlgebraicCycle.intersection
        (CycleGroup.toAlgebraicCycle
          ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0)) (r + 1)
          (@Scheme.IdealSheafData.associatedCycle
            (P ⨯ Over.mk (ProjectiveLine.toSpec k)).left
            (LocallyOfFiniteType.isLocallyNoetherian
              (P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom) C'
            ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
              (fun _ ↦ 0)) (r + 1)))
        (CycleGroup.toAlgebraicCycle
          ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0)) ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).dimension : ℤ)
          (@Scheme.IdealSheafData.associatedCycle
            (P ⨯ Over.mk (ProjectiveLine.toSpec k)).left
            (LocallyOfFiniteType.isLocallyNoetherian
              (P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom)
            (comap i.left.ker
              (prod.fst : P ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ P).left)
            ((P ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
              (fun _ ↦ 0)) ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).dimension : ℤ))) hC'proper)
    , alpha = AlgebraicCycle.map
      (prod.fst : X ⨯ Over.mk (ProjectiveLine.toSpec k) ⟶ X).left
      ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction (fun _ ↦ 0))
      (X.hom.relativeDimensionFunction (fun _ ↦ 0))
      (AlgebraicCycle.intersection beta
        (CycleGroup.toAlgebraicCycle
          ((X ⨯ Over.mk (ProjectiveLine.toSpec k)).hom.relativeDimensionFunction
            (fun _ ↦ 0)) (X.dimension : ℤ)
          (AlgebraicGeometry.ProjectiveLineFiber.cycle X (ProjectiveLine.zeroPoint k)))
        (AlgebraicGeometry.ProjectiveLineFiber.intersectsProperly_zeroFiber X P i r hr C' C hC' hC hCfiber
          hCproper hC'proper beta hBetaView)))
