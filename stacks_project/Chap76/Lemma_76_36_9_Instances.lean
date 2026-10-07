module

public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Lemma_75_26_8_GeometricFibres
public import stacks_project.Chap76.Lemma_76_29_3_ReducedFiberLocus

/-!
# Finite étaleness of the Stein second factor

For a proper morphism of algebraic spaces that is of finite presentation, flat,
and has geometrically reduced fibres, the structure morphism of the relative
normalization is finite and étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The structure morphism of the relative normalization of a proper morphism of
algebraic spaces that is of finite presentation, flat, and has reduced geometric
fibres is finite. -/
instance instIsFinite_fromNormalization_of_flat_geometricallyReduced
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [FinitePresentation f] [Flat f] [HasReducedGeometricFibres f] :
    IsFinite (fromNormalization f) :=
  sorry

/-- The structure morphism of the relative normalization of a proper morphism of
algebraic spaces that is of finite presentation, flat, and has reduced geometric
fibres is étale. -/
instance instEtale_fromNormalization_of_flat_geometricallyReduced
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [FinitePresentation f] [Flat f] [HasReducedGeometricFibres f] :
    Etale (fromNormalization f) :=
  sorry

/-- If a proper morphism of algebraic spaces is of finite presentation, flat, and
the geometrically reduced fibre locus is all of `Points Y`, then the structure
morphism of the relative normalization is finite. -/
theorem isFinite_fromNormalization_of_geometricallyReducedFiberLocus
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [FinitePresentation f] [Flat f]
    (h_reduced : geometricallyReducedFiberLocus f = Set.univ) :
    IsFinite (fromNormalization f) :=
  sorry

/-- If a proper morphism of algebraic spaces is of finite presentation, flat, and
the geometrically reduced fibre locus is all of `Points Y`, then the structure
morphism of the relative normalization is étale. -/
theorem etale_fromNormalization_of_geometricallyReducedFiberLocus
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [FinitePresentation f] [Flat f]
    (h_reduced : geometricallyReducedFiberLocus f = Set.univ) :
    Etale (fromNormalization f) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
