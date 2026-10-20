module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Flat.BaseChange
import StacksCheckRecall

/-!
# Base change of flat morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 88.13.6 (1): flatness is preserved by base change when the induced
morphism on reductions is locally of finite type. -/
@[stacks 0GCE] #check (AlgebraicGeometry.FormalAlgebraicSpace.Flat.pullback_snd :
    ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (RY : ReductionData Y) (RZ : ReductionData Z)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [Flat f]
    [AlgebraicSpace.LocallyOfFiniteType (RZ.map RY g)]
    [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)],
    Flat (pullback.snd f g))

#check (AlgebraicGeometry.FormalAlgebraicSpace.Flat.of_isPullback :
    ∀ {S : Scheme.{u}} {X Y Z W : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    (RY : ReductionData Y) (RZ : ReductionData Z)
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) [Flat f]
    [AlgebraicSpace.LocallyOfFiniteType (RZ.map RY g)],
    Flat snd)

/- Lemma 88.13.6 (2): the base change of a flat, locally of finite type
morphism is flat and locally of finite type. -/
@[stacks 0GCE] #check (AlgebraicGeometry.FormalAlgebraicSpace.Flat.pullback_snd_flat_and_locallyOfFiniteType :
    ∀
    {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [Flat f]
    [LocallyOfFiniteType f] [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)],
    Flat (pullback.snd f g) ∧ LocallyOfFiniteType (pullback.snd f g))

#check (AlgebraicGeometry.FormalAlgebraicSpace.Flat.pullback_snd_of_locallyOfFiniteType :
    ∀
    {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [Flat f]
    [LocallyOfFiniteType f] [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)],
    Flat (pullback.snd f g))

#check (AlgebraicGeometry.FormalAlgebraicSpace.Flat.of_isPullback_of_locallyOfFiniteType :
    ∀
    {S : Scheme.{u}} {X Y Z W : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) [Flat f] [LocallyOfFiniteType f],
    Flat snd)
