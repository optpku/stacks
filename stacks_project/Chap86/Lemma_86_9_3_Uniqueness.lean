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

/-- Two relative dualizing complexes for the same proper, flat, finitely presented
morphism of algebraic spaces admit a unique isomorphism of underlying complexes in
`D(𝒪_X)` making the traces commute. -/
theorem existsUniqueIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [Proper f] [Flat f] [FinitePresentation f]
    (C D : RelativeDualizingComplex f) :
    ∃! e : C.complex ≅ D.complex,
      C.trace = (moduleDerivedPushforward f).map e.hom ≫ D.trace := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeDualizingComplex
