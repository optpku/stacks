/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Spectral
import StacksCheckRecall

/-!
# Open spectral coverings of algebraic stacks with quasi-compact diagonal

An algebraic stack whose absolute diagonal is quasi-compact has an open covering
of its space of points by spectral spaces, and in particular that space is sober.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open TopologicalSpace
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.30.3 (1): Let `X` be an algebraic stack whose diagonal is quasi-compact.
Then there is an open covering `|X| = ⋃ i, U i` with each `U i` spectral. -/
@[stacks 0DQQ]
#check (AlgebraicGeometry.AlgebraicStack.exists_isOpenCover_spectral_of_quasiCompact_diagonal :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))),
    ∃ (ι : Type (u + 1)) (U : ι → Opens (Points X)),
      IsOpenCover U ∧ ∀ i, SpectralSpace (U i))

/- Lemma 101.30.3 (2): In particular, if `X` is an algebraic stack whose diagonal is
quasi-compact, then `|X|` is a sober topological space. -/
@[stacks 0DQQ]
#check (AlgebraicGeometry.AlgebraicStack.sober_of_quasiCompact_diagonal :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))),
    T0Space (Points X) ∧ QuasiSober (Points X))

/- Every irreducible closed subset of `Points X` has a unique generic point when the
absolute diagonal of `X` is quasi-compact. -/
#check (AlgebraicGeometry.AlgebraicStack.existsUnique_isGenericPoint_of_quasiCompact_diagonal :
  ∀ {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X)))
    {T : Set (Points X)} (hT_irred : IsIrreducible T) (hT_closed : IsClosed T),
    ∃! x : Points X, IsGenericPoint x T)

/- A quasi-separated algebraic stack admits an open covering of `|X|` by spectral
spaces. -/
#check (AlgebraicGeometry.AlgebraicStack.IsQuasiSeparated.exists_isOpenCover_spectral :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiSeparated X],
    ∃ (ι : Type (u + 1)) (U : ι → Opens (Points X)),
      IsOpenCover U ∧ ∀ i, SpectralSpace (U i))

/- The space of points of a quasi-separated algebraic stack is Kolmogorov. -/
#check (AlgebraicGeometry.AlgebraicStack.IsQuasiSeparated.instT0SpacePoints :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiSeparated X], T0Space (Points X))

/- The space of points of a quasi-separated algebraic stack is quasi-sober. -/
#check (AlgebraicGeometry.AlgebraicStack.IsQuasiSeparated.instQuasiSoberPoints :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiSeparated X], QuasiSober (Points X))

end AlgebraicGeometry.AlgebraicStack
