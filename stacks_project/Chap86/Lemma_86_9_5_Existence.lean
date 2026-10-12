/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap86.Definition_86_9_1_RelativeDualizing

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived
open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex

/-- A proper, flat, finitely presented morphism of algebraic spaces admits a relative
dualizing complex. -/
theorem nonempty {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] :
    Nonempty (RelativeDualizingComplex f) := sorry

/-- Existence of a relative dualizing complex is equivalent to existence of a
`Y`-perfect pair `(ω, τ)` satisfying the affine cartesian base-change condition. -/
theorem nonempty_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f] :
    Nonempty (RelativeDualizingComplex f) ↔
      ∃ (ω : ModuleDerived X)
        (τ : (moduleDerivedPushforward f).obj ω ⟶ derivedStructureSheaf Y),
        IsPerfectRelativeTo f ω ∧ affineBaseChangeCondition f ω τ := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex
