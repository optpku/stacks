module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.FrobeniusGeneration
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open CategoryTheory TopologicalSpace

universe u

/- Proposition 64.34.1. For a smooth geometrically irreducible projective curve
 over a finite field, all Frobenius elements at finitely many closed points
 topologically generate the étale fundamental group. -/
@[stacks 03W5] #check
  (AlgebraicGeometry.SchemeOverField.exists_finset_etaleGeometricFrobenius_topologicallyGenerate :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Finite k] [Curve X]
      [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
      [ConnectedSpace X.left] (xbar : GeometricPoint X.left),
      ∃ S : Finset (closedPoints X.left),
        (Subgroup.closure
          (⋃ v ∈ S, etaleGeometricFrobeniusSet X xbar v)).topologicalClosure = ⊤)

#check
  (AlgebraicGeometry.SchemeOverField.exists_finset_etaleGeometricFrobenius_normalClosure :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Finite k] [Curve X]
      [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
      [ConnectedSpace X.left] (xbar : GeometricPoint X.left),
      ∃ S : Finset (closedPoints X.left),
        ∀ F : S → Aut (GeometricPoint.finiteFiber xbar),
          (∀ v : S, F v ∈ etaleGeometricFrobeniusSet X xbar v.1) →
            (Subgroup.normalClosure (Set.range F)).topologicalClosure = ⊤)

#check
  (AlgebraicGeometry.SchemeOverField.etaleGeometricFrobenius_topologicallyGenerate_iff_normalClosure :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Finite k]
      [ConnectedSpace X.left] [LocallyOfFiniteType X.hom]
      (xbar : GeometricPoint X.left) (S : Finset (closedPoints X.left)),
      (Subgroup.closure
        (⋃ v ∈ S, etaleGeometricFrobeniusSet X xbar v)).topologicalClosure = ⊤ ↔
        ∀ F : S → Aut (GeometricPoint.finiteFiber xbar),
          (∀ v : S, F v ∈ etaleGeometricFrobeniusSet X xbar v.1) →
            (Subgroup.normalClosure (Set.range F)).topologicalClosure = ⊤)
