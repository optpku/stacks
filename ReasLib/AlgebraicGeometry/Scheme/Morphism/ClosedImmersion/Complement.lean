/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Complements of closed immersions

This file defines the open subscheme complementary to the image of a closed immersion.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The open complement of the image of a closed immersion of schemes. -/
def closedImmersionComplement {S Z : Scheme.{u}} (i : Z ⟶ S) [IsClosedImmersion i] : S.Opens :=
  ⟨(Set.range ⇑(CategoryTheory.ConcreteCategory.hom i.base))ᶜ,
    (isOpen_compl_iff).2 (IsClosedImmersion.isClosedEmbedding i).isClosed_range⟩

end AlgebraicGeometry
