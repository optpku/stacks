module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSmooth
import StacksCheckRecall

/-!
# Composition of rig-smooth morphisms

The composition of rig-smooth morphisms of locally Noetherian formal algebraic
spaces is again rig-smooth.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 88.18.4: let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `f` and
`g` are rig-smooth, then so is `g ∘ f`. In Lean composition this is
`RigSmooth (f ≫ g)`. -/
@[stacks 0GCS] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigSmooth.comp :
  ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [RigSmooth f] [RigSmooth g], RigSmooth (f ≫ g))
