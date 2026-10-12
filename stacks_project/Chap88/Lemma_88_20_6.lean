/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_20_1

/-!
# Composition of rig-étale morphisms

The composition of rig-étale morphisms of locally Noetherian formal algebraic
spaces is again rig-étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigEtale

/-- Lemma 88.20.6: let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `f` and
`g` are rig-étale, then so is `g ∘ f`. In Lean composition this is
`RigEtale (f ≫ g)`. -/
@[stacks 0GD2]
instance comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [RigEtale f] [RigEtale g] : RigEtale (f ≫ g) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigEtale
