/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Graph
public import ReasLib.AlgebraicGeometry.Correspondence.Graph
public import ReasLib.AlgebraicGeometry.Correspondence.Transpose
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Graph

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry

namespace SchemeOverField

/-- The transposed graph map is the graph map followed by exchange of the product factors. -/
noncomputable def transposedGraph {k : Type u} [Field k]
    {X Y : SchemeOverField k} (f : Y ⟶ X) : Y.left ⟶ (Y ⨯ X).left :=
  graph f ≫ (CategoryTheory.Over.prodLeftIsoPullback X Y).inv ≫
    (Limits.prod.braiding X Y).hom.left

/-- The first projection of the transposed graph is the identity of `Y`. -/
theorem transposedGraph_fst {k : Type u} [Field k]
    {X Y : SchemeOverField k} (f : Y ⟶ X) :
    transposedGraph f ≫ (Limits.prod.fst : Y ⨯ X ⟶ Y).left = 𝟙 Y.left := sorry

/-- The second projection of the transposed graph is `f`. -/
theorem transposedGraph_snd {k : Type u} [Field k]
    {X Y : SchemeOverField k} (f : Y ⟶ X) :
    transposedGraph f ≫ (Limits.prod.snd : Y ⨯ X ⟶ X).left = f.left := sorry

/-- The transposed graph is a closed immersion when `X` is separated over the field. -/
instance transposedGraph_isClosedImmersion {k : Type u} [Field k]
    {X Y : SchemeOverField k} [IsSeparated X.hom] (f : Y ⟶ X) :
    IsClosedImmersion (transposedGraph f) := sorry

end SchemeOverField

namespace AlgebraicCycle

/-- The transposed graph cycle is obtained from the graph cycle by exchanging factors. -/
noncomputable def transposedGraph {k : Type u} [Field k] {X Y : SchemeOverField k}
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] (f : Y ⟶ X) :
    AlgebraicCycle (Y ⨯ X).left ℤ :=
  swapEquiv X Y (map (CategoryTheory.Over.prodLeftIsoPullback X Y).inv
    (fun _ ↦ (0 : ℤ)) (fun _ ↦ (0 : ℤ)) (graph f))

/-- Exchanging the factors of a graph cycle gives its transposed graph cycle. -/
theorem transpose_graph {k : Type u} [Field k] {X Y : SchemeOverField k}
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] (f : Y ⟶ X) :
    swapEquiv X Y (map (CategoryTheory.Over.prodLeftIsoPullback X Y).inv
      (fun _ ↦ (0 : ℤ)) (fun _ ↦ (0 : ℤ)) (graph f)) = transposedGraph f := sorry

end AlgebraicCycle

namespace CycleGroup

/-- The graph cycle is homogeneous of dimension `e` when its source is equidimensional of
dimension `e`. -/
theorem graph_mem_dimensionSubgroup {k : Type u} [Field k]
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] [EquidimensionalSpace Y.left]
    (e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    AlgebraicCycle.map (CategoryTheory.Over.prodLeftIsoPullback X Y).inv
        (fun _ ↦ (0 : ℤ)) (fun _ ↦ (0 : ℤ)) (AlgebraicCycle.graph f) ∈
      AlgebraicCycle.dimensionSubgroup
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) ((e : ℤ) - 0) := sorry

/-- The graph of `f` as a homogeneous cycle representing a degree-zero correspondence. -/
noncomputable def graph {k : Type u} [Field k]
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] [EquidimensionalSpace Y.left]
    (e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    CycleGroup (X ⨯ Y).left
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) ((e : ℤ) - 0) :=
  ⟨AlgebraicCycle.map (CategoryTheory.Over.prodLeftIsoPullback X Y).inv
      (fun _ ↦ (0 : ℤ)) (fun _ ↦ (0 : ℤ)) (AlgebraicCycle.graph f),
    graph_mem_dimensionSubgroup e hYdim f⟩

/-- Forgetting the grading of the homogeneous graph cycle gives the raw graph cycle. -/
theorem toAlgebraicCycle_graph {k : Type u} [Field k]
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] [EquidimensionalSpace Y.left]
    (e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0))
      ((e : ℤ) - 0) (graph e hYdim f) =
        AlgebraicCycle.map (CategoryTheory.Over.prodLeftIsoPullback X Y).inv
          (fun _ ↦ (0 : ℤ)) (fun _ ↦ (0 : ℤ)) (AlgebraicCycle.graph f) := sorry

/-- The transposed graph cycle has the grading of a degree-`d - e` correspondence from
`Y` to `X`. -/
theorem transposedGraph_mem_dimensionSubgroup {k : Type u} [Field k]
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    AlgebraicCycle.transposedGraph f ∈ AlgebraicCycle.dimensionSubgroup
      ((Y ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0))
      ((d : ℤ) - ((d : ℤ) - (e : ℤ) + 0)) := sorry

/-- The transposed graph as a homogeneous cycle of the shifted correspondence degree. -/
noncomputable def transposedGraph {k : Type u} [Field k]
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    CycleGroup (Y ⨯ X).left
      ((Y ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0))
      ((d : ℤ) - ((d : ℤ) - (e : ℤ) + 0)) :=
  ⟨AlgebraicCycle.transposedGraph f,
    transposedGraph_mem_dimensionSubgroup d e hYdim f⟩

/-- Forgetting the grading of the homogeneous transposed graph gives its raw cycle. -/
theorem toAlgebraicCycle_transposedGraph {k : Type u} [Field k]
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    toAlgebraicCycle ((Y ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0))
      ((d : ℤ) - ((d : ℤ) - (e : ℤ) + 0)) (transposedGraph d e hYdim f) =
        AlgebraicCycle.transposedGraph f := sorry

end CycleGroup

namespace ChowGroup

/-- The integral Chow class of a graph in the grading for a degree-zero correspondence. -/
noncomputable def graphClass {k : Type u} [Field k]
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] [EquidimensionalSpace Y.left]
    (e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    @ChowGroup (X ⨯ Y).left (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
      ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance ((e : ℤ) - 0) :=
  let hBase : IsLocallyNoetherian (Spec (CommRingCat.of k)) :=
    @UniversallyCatenary.toIsLocallyNoetherian _
      (@instUniversallyCatenarySpec k _
        (@instUniversallyCatenaryRingOfField.{u, u} k _))
  let hProduct : IsLocallyNoetherian (X ⨯ Y).left :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ (X ⨯ Y).hom inferInstance hBase
  @chowClass (X ⨯ Y).left hProduct
    ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance ((e : ℤ) - 0)
    (CycleGroup.graph e hYdim f)

/-- The graph Chow class is represented by the homogeneous graph cycle. -/
theorem graphClass_def {k : Type u} [Field k]
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] [EquidimensionalSpace Y.left]
    (e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    graphClass e hYdim f =
      @chowClass (X ⨯ Y).left (LocallyOfFiniteType.isLocallyNoetherian (X ⨯ Y).hom)
        ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance ((e : ℤ) - 0)
        (CycleGroup.graph e hYdim f) := sorry

/-- The integral Chow class of the transposed graph in the shifted correspondence grading. -/
noncomputable def transposedGraphClass {k : Type u} [Field k]
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    @ChowGroup (Y ⨯ X).left (LocallyOfFiniteType.isLocallyNoetherian (Y ⨯ X).hom)
      ((Y ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance
      ((d : ℤ) - ((d : ℤ) - (e : ℤ) + 0)) :=
  let hBase : IsLocallyNoetherian (Spec (CommRingCat.of k)) :=
    @UniversallyCatenary.toIsLocallyNoetherian _
      (@instUniversallyCatenarySpec k _
        (@instUniversallyCatenaryRingOfField.{u, u} k _))
  let hProduct : IsLocallyNoetherian (Y ⨯ X).left :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ (Y ⨯ X).hom inferInstance hBase
  @chowClass (Y ⨯ X).left hProduct
    ((Y ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance
    ((d : ℤ) - ((d : ℤ) - (e : ℤ) + 0))
    (CycleGroup.transposedGraph d e hYdim f)

/-- The transposed-graph Chow class is represented by its homogeneous cycle. -/
theorem transposedGraphClass_def {k : Type u} [Field k]
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    transposedGraphClass d e hYdim f =
      @chowClass (Y ⨯ X).left (LocallyOfFiniteType.isLocallyNoetherian (Y ⨯ X).hom)
        ((Y ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0)) inferInstance
        ((d : ℤ) - ((d : ℤ) - (e : ℤ) + 0))
        (CycleGroup.transposedGraph d e hYdim f) := sorry

end ChowGroup

namespace Correspondence

/-- The rational Chow realization class of the canonical graph correspondence. -/
noncomputable def graphClass {k : Type u} [Field k]
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] [EquidimensionalSpace Y.left]
    (e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    RationalChowRealization X Y e 0 :=
  (1 : ℚ) ⊗ₜ[ℤ] ChowGroup.graphClass.{u, u} e hYdim f

/-- The rational graph class is the pure tensor of its integral Chow class. -/
theorem graphClass_def {k : Type u} [Field k]
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] [EquidimensionalSpace Y.left]
    (e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    graphClass e hYdim f = (1 : ℚ) ⊗ₜ[ℤ] ChowGroup.graphClass.{u, u} e hYdim f := sorry

/-- The rational Chow realization class represented by the transposed graph. -/
noncomputable def transposedGraphClass {k : Type u} [Field k]
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    RationalChowRealization Y X d ((d : ℤ) - (e : ℤ) + 0) :=
  (1 : ℚ) ⊗ₜ[ℤ] ChowGroup.transposedGraphClass.{u, u} d e hYdim f

/-- The rational transposed-graph class is the pure tensor of its integral Chow class. -/
theorem transposedGraphClass_def {k : Type u} [Field k]
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    transposedGraphClass d e hYdim f =
      (1 : ℚ) ⊗ₜ[ℤ] ChowGroup.transposedGraphClass.{u, u} d e hYdim f := sorry

/-- Realization-level transpose sends the rational graph class to the rational class of the
transposed graph. -/
theorem realizationTranspose_graph {k : Type u} [Field k]
    (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    realizationTranspose X Y d e hXdim hYdim 0 (graphClass e hYdim f) =
      transposedGraphClass d e hYdim f := sorry

/-- The Chow realization of the canonical rational graph is its rational graph class. -/
theorem realizationEquiv_rationalGraph {k : Type u} [Field k]
    (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (e : ℕ) (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    realizationEquiv X Y e hYdim 0 (rationalGraph f) = graphClass e hYdim f := sorry

/-- The transposed graph correspondence is obtained by inverse realization of its rational
transposed-graph Chow class. -/
noncomputable def transposedGraph {k : Type u} [Field k]
    (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    Rational Y X ((d : ℤ) - (e : ℤ) + 0) :=
  (realizationEquiv Y X d hXdim ((d : ℤ) - (e : ℤ) + 0)).symm
    (transposedGraphClass d e hYdim f)

/-- Transpose carries the canonical rational graph correspondence to the correspondence
represented by the transposed graph. -/
theorem transpose_graph {k : Type u} [Field k]
    (X Y : SchemeOverField k)
    [Smooth X.hom] [Projective X.hom] [EquidimensionalSpace X.left]
    [Smooth Y.hom] [Projective Y.hom] [EquidimensionalSpace Y.left]
    (d e : ℕ) (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) :
    transpose X Y d e hXdim hYdim 0 (rationalGraph f) =
      transposedGraph X Y d e hXdim hYdim f := sorry

end Correspondence

end AlgebraicGeometry
