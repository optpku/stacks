/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_18_1

/-!
# Composition of rig-smooth morphisms

The composition of rig-smooth morphisms of locally Noetherian formal algebraic
spaces is again rig-smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigSmooth

/-- Lemma 88.18.4: let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `f` and
`g` are rig-smooth, then so is `g ∘ f`. In Lean composition this is
`RigSmooth (f ≫ g)`. -/
@[stacks 0GCS]
instance comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [RigSmooth f] [RigSmooth g] : RigSmooth (f ≫ g) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigSmooth
