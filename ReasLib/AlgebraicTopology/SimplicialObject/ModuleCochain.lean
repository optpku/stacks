module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# Cochain complexes of simplicial modules

The alternating-face complex of a simplicial module extends to a cochain
complex indexed by the integers.
-/

@[expose] public section

open CategoryTheory AlgebraicTopology HomologicalComplex

universe u

/-- The alternating-face complex of a simplicial module, extended to integer cohomological degrees. -/
noncomputable def simplicialModuleToCochain (C : Type u) [CommRing C] :
    SimplicialObject (ModuleCat.{u} C) ⥤ CochainComplex (ModuleCat.{u} C) ℤ :=
  alternatingFaceMapComplex (ModuleCat.{u} C) ⋙
    ComplexShape.embeddingDownNat.extendFunctor (ModuleCat.{u} C)
