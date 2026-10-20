module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Definition 41.9.3 (1): for a quasi-coherent module sheaf `ℱ`, flatness over `Y` at
`x : X` means that the stalk `ℱₓ`, viewed through the induced local-ring map, is flat over
the local ring of `Y` at the image of `x`. The canonical predicate applies to any module sheaf. -/
@[stacks 0253] #check
  (AlgebraicGeometry.Scheme.Modules.flatOverAt :
    {X Y : Scheme.{u}} → X.Modules → (X ⟶ Y) → X → Prop)

/- Definition 41.9.3 (2): a scheme morphism is flat at `x : X` when its induced map on
local rings at `x` and its image is flat. -/
@[stacks 0253] #check
  (AlgebraicGeometry.Scheme.Hom.flatAt :
    {X Y : Scheme.{u}} → (X ⟶ Y) → X → Prop)

/- Definition 41.9.3 (3): a scheme morphism is flat exactly when it is flat at every source
point. -/
@[stacks 0253] #check
  (AlgebraicGeometry.Scheme.Hom.flat_iff_forall_flatAt :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      Flat f ↔ ∀ x : X, AlgebraicGeometry.Scheme.Hom.flatAt f x)

/- Definition 41.9.3 (4): a faithfully flat scheme morphism is one that is both flat and
surjective. -/
@[stacks 0253] #check
  (AlgebraicGeometry.faithfullyFlatMorphismProperty :
    CategoryTheory.MorphismProperty Scheme.{u})
