module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective
import StacksCheckRecall

/-!
# Permanence of rig-surjectivity

If a composite of locally finite type morphisms of locally Noetherian formal
algebraic spaces is rig-surjective, then so is the second factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace

universe u

/- Lemma 88.21.6: Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of formal algebraic spaces over `S`. Assume `X`, `Y`, `Z` locally
Noetherian and `f` and `g` locally of finite type. If `g ∘ f : X ⟶ Z` is
rig-surjective, so is `g : Y ⟶ Z`. In Lean composition this is the implication
`RigSurjective (f ≫ g) → RigSurjective g`. -/
@[stacks 0AQT] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [RigSurjective (f ≫ g)],
    RigSurjective g)
