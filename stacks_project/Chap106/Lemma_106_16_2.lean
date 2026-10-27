/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.QCoh.AffineTensor
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Limits FiberedCategoryOver.Groupoids
open scoped Bicategory TensorProduct

universe u

/- Lemma 106.16.2. A right exact tensor functor preserving direct sums,
evaluated on modules pushed forward from an affine scheme, is tensoring with
the evaluated structure algebra via the canonical coordinate-ring map. -/
@[stacks 0GRK] #check (AlgebraicGeometry.GroupoidsOver.QCoh.affineTensorFunctor :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {B : Type u} [CommRing B] (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided]
    [PreservesFiniteColimits F]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    {U : Over S} [IsAffine U.left] (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g],
    IsIso (AlgebraicGeometry.GroupoidsOver.QCoh.affineTensorComparison F g))
