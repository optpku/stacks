module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective
import StacksCheckRecall

/-!
# Left cancellation of rig-surjectivity along a monomorphism

If a composite of locally finite type morphisms of locally Noetherian formal
algebraic spaces is rig-surjective and the second factor is a monomorphism,
then the first factor is rig-surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace

universe u

/- Lemma 88.21.5: Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms locally of finite type of locally Noetherian formal algebraic spaces
over `S`. If `g ∘ f` is rig-surjective and `g` is a monomorphism, then `f` is
rig-surjective. In Lean composition this is the implication
`RigSurjective (f ≫ g) → Mono g → RigSurjective f`. -/
@[stacks 0GH5] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective.of_comp_mono :
    ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [RigSurjective (f ≫ g)] [Mono g],
    RigSurjective f)
