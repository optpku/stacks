/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.Approximation
public import Mathlib.CategoryTheory.Equivalence

/-! # Formal existence for coherent sheaves

Maximal-adic restriction of flat coherent sheaves with proper support is an
equivalence for separated morphisms of finite presentation over a locally
Noetherian base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

/-- For a separated morphism of finite presentation over a locally Noetherian
scheme, maximal-adic restriction of flat coherent sheaves with proper support is
an equivalence. The source consists of objects over Noetherian complete local
algebras with finite-type residue field and morphisms inducing local
`S`-algebra homomorphisms. -/
instance instApproximationIsEquivalence {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f] [Separated f] :
    (AlgebraicGeometry.GroupoidsOver.approximation (toGroupoids f)).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
