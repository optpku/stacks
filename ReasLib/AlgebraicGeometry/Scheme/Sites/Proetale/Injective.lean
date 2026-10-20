module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Abelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Injectivity under pro-étale relocalization

Inverse image from the big pro-étale site to a small pro-étale site preserves
injective abelian sheaves and unbounded K-injective complexes.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- Inverse image from the big pro-étale site over `S` to the small pro-étale
site of `T` preserves injective abelian sheaves. -/
instance iInverseImage_preservesInjectiveObjects
    {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}] :
    (iInverseImage f).PreservesInjectiveObjects := sorry

/-- Inverse image from the big pro-étale site over `S` to the small pro-étale
site of `T` preserves unbounded K-injective cochain complexes of abelian sheaves. -/
instance iInverseImage_obj_isKInjective
    {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    (I : CochainComplex
      (Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1}) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((iInverseImage f).mapHomologicalComplex (up ℤ)).obj I) := sorry

end AlgebraicGeometry.Scheme.ProEt
