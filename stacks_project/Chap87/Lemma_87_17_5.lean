/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Definition_87_17_4_QuasiCompact
public import stacks_project.Chap80.Definition_80_4_1_Relative

/-!
# Quasi-compact morphisms of formal algebraic spaces versus Bootstrap transfer

A morphism of formal algebraic spaces representable by algebraic spaces is
quasi-compact in the sense of Definition 87.17.4 if and only if it is
quasi-compact in the sense of Bootstrap, Definition 80.4.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.QuasiCompact

/-- Lemma 87.17.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S` which is representable by algebraic spaces.
Then `f` is quasi-compact in the sense of Definition 87.17.4 if and only if
`f` is quasi-compact in the sense of Bootstrap, Definition 80.4.1. -/
@[stacks 0AM2]
theorem iff_relativeAlgebraicSpaces {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [Reduction X] [Reduction Y] (f : X ⟶ Y)
    (hf : AlgebraicSpace.representableByAlgebraicSpaces f) :
    QuasiCompact f ↔
      AlgebraicSpace.relativeAlgebraicSpaces (@AlgebraicSpace.QuasiCompact S) f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.QuasiCompact
