/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import stacks_project.Chap81.Lemma_81_11_1_Restriction

/-!
# Lemma 81.11.1

In Situation 81.10.6, the canonical glueing functor `Over X ⥤ category f i`
restricts to equivalences on algebraic spaces affine over `X`, on closed
immersions over `X`, and on finite morphisms over `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalGlueing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormalGlueing

/-- Lemma 81.11.1 (1): In Situation 81.10.6 the functor (81.11.0.1) restricts to
an equivalence from the category of algebraic spaces affine over `X` to the full
subcategory of `Spaces(Y → X, Z)` consisting of `(U' ← V' → Y')` with
`U' ⟶ U`, `V' ⟶ V`, and `Y' ⟶ Y` affine. -/
@[stacks 0AF4, instance]
instance affineOverFunctor_isEquivalence {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (affineOverFunctor f i).IsEquivalence :=
  sorry

/-- Lemma 81.11.1 (2): In Situation 81.10.6 the functor (81.11.0.1) restricts to
an equivalence from the category of closed immersions `X' ⟶ X` to the full
subcategory of `Spaces(Y → X, Z)` consisting of `(U' ← V' → Y')` with
`U' ⟶ U`, `V' ⟶ V`, and `Y' ⟶ Y` closed immersions. -/
@[stacks 0AF4, instance]
instance closedImmersionOverFunctor_isEquivalence {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (closedImmersionOverFunctor f i).IsEquivalence :=
  sorry

/-- Lemma 81.11.1 (3): In Situation 81.10.6 the functor (81.11.0.1) restricts to
an equivalence from the category of finite morphisms `X' ⟶ X` to the full
subcategory of `Spaces(Y → X, Z)` consisting of `(U' ← V' → Y')` with
`U' ⟶ U`, `V' ⟶ V`, and `Y' ⟶ Y` finite. -/
@[stacks 0AF4, instance]
instance finiteOverFunctor_isEquivalence {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (finiteOverFunctor f i).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormalGlueing
