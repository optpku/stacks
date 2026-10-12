/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_13_4

/-!
# Composition of flat morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 88.13.7: Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `f` and
`g` are flat, then so is `g ∘ f`. In Lean composition this is
`Flat f → Flat g → Flat (f ≫ g)`. -/
@[stacks 0GCF]
instance Flat.comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g] : Flat (f ≫ g) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
