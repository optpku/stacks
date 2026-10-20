module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigFlat.Composition
import StacksCheckRecall

/-!
# Composition of rig-flat morphisms

The composition of rig-flat morphisms of locally Noetherian formal algebraic
spaces is again rig-flat.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 88.16.4: let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `f` and
`g` are rig-flat, then so is `g ∘ f`. In Lean composition this is
`RigFlat (f ≫ g)`. -/
@[stacks 0GH0] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigFlat.comp :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [RigFlat f] [RigFlat g], RigFlat (f ≫ g))
