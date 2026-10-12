/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Remark_75_9_5_AffineDiagonal
public import stacks_project.Chap75.Lemma_75_11_2_Coherator
public import stacks_project.Chap75.«75_5_1_1_Comparison»

/-!
# Comparison for quasi-compact algebraic spaces with affine diagonal

The canonical comparison from the derived category of quasi-coherent modules on a
quasi-compact algebraic space with affine diagonal over the terminal scheme is an
equivalence, with the restricted derived coherator as quasi-inverse.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- On a quasi-compact algebraic space with affine diagonal over the terminal scheme,
the canonical comparison `DerivedCategory (QCoh X) ⥤ DerivedQCoh X` and the restricted
derived coherator `inclusion X ⋙ QCoh.Derived.coherator X` are quasi-inverse. -/
theorem comparison_isQuasiInverse_of_compact_affineDiagonal {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsQuasiCompact X] [IsAbsolutelyAffineDiagonal X] :
    (comparison X).IsQuasiInverse (inclusion X ⋙ QCoh.Derived.coherator X) :=
  sorry

/-- On a quasi-compact algebraic space with affine diagonal over the terminal scheme,
the canonical comparison from derived quasi-coherent modules to ambient derived modules
with quasi-coherent cohomology is an equivalence. -/
instance comparisonIsEquivalenceOfCompactAffineDiagonal {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyAffineDiagonal X] :
    (comparison X).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
