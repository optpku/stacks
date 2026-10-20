module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective
import StacksCheckRecall

/-!
# Base change of rig-surjective morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 88.21.4: let `S` be a scheme, and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of formal algebraic spaces over `S`. Assume `X`, `Y`, `Z` are locally
Noetherian and that `f` and `g` are locally of finite type. If `f` is
rig-surjective, then the base change `Z ×_Y X ⟶ Z`, realized as
`pullback.snd f g : pullback f g ⟶ Z` up to the canonical symmetry of fibre
products, is rig-surjective. -/
@[stacks 0AQS] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective.pullback_snd :
    ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] [RigSurjective f],
    RigSurjective (pullback.snd f g))
