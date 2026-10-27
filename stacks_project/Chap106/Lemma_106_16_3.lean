/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.QCoh.UniversallyInjective
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Limits
open FiberedCategoryOver.Groupoids
open scoped Bicategory TensorProduct

universe u

/- Lemma 106.16.3. Notation as in Lemma 106.16.2. Assume `X` is Noetherian and
`g` is surjective and flat. Then the structure map `B → C` is universally
injective as a map of `B`-modules. -/
@[stacks 0GRL] #check (AlgebraicGeometry.GroupoidsOver.QCoh.algebraMap_universallyInjective :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.IsNoetherian X]
    [Groupoids.Hom.Affine (diagonal.{u + 1, u, u + 1} X)]
    {B : Type u} [CommRing B]
    (F : QCoh X ⥤ ModuleCat.{u} B) [F.Braided]
    [PreservesFiniteColimits F]
    [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]
    {U : Over S} [IsAffine U.left]
    (g : GroupoidsOver.slice U ⟶ X)
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    [AlgebraicStack.Surjective g] [AlgebraicStack.Flat g],
    LinearMap.UniversallyInjective.{u, u, u, u}
      (AlgebraicGeometry.GroupoidsOver.QCoh.algebraLinearMap F g))
