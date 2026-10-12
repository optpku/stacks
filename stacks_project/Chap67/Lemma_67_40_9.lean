/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.Data.List.TFAE
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_40_1_Proper

/-!
# Separatedness via the relative diagonal

A morphism of algebraic spaces is separated iff its relative diagonal is
universally closed, iff that same diagonal is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Separated

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 67.40.9: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `Separated f`,
`UniversallyClosed (pullback.diagonal f)`, and `Proper (pullback.diagonal f)`. -/
@[stacks 04Y0]
theorem tfae (f : X ⟶ Y) :
    List.TFAE [Separated f, UniversallyClosed (pullback.diagonal f),
      Proper (pullback.diagonal f)] :=
  sorry

/-- A morphism of algebraic spaces is separated if and only if its relative
diagonal is universally closed. -/
theorem iff_universallyClosed_diagonal (f : X ⟶ Y) :
    Separated f ↔ UniversallyClosed (pullback.diagonal f) :=
  sorry

/-- A morphism of algebraic spaces is separated if and only if its relative
diagonal is proper. -/
theorem iff_proper_diagonal (f : X ⟶ Y) :
    Separated f ↔ Proper (pullback.diagonal f) :=
  sorry

/-- The relative diagonal of a separated morphism of algebraic spaces is
universally closed. -/
instance universallyClosed_diagonal {f : X ⟶ Y} [Separated f] :
    UniversallyClosed (pullback.diagonal f) :=
  sorry

/-- The relative diagonal of a separated morphism of algebraic spaces is
proper. -/
instance proper_diagonal {f : X ⟶ Y} [Separated f] :
    Proper (pullback.diagonal f) :=
  sorry

end Separated

end AlgebraicGeometry.AlgebraicSpace
