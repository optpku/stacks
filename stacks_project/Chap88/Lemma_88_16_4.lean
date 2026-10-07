module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_16_1

/-!
# Composition of rig-flat morphisms

The composition of rig-flat morphisms of locally Noetherian formal algebraic
spaces is again rig-flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigFlat

/-- Lemma 88.16.4: let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `f` and
`g` are rig-flat, then so is `g ∘ f`. In Lean composition this is
`RigFlat (f ≫ g)`. -/
@[stacks 0GH0]
instance comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [RigFlat f] [RigFlat g] : RigFlat (f ≫ g) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigFlat
