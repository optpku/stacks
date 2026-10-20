module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Base change of rig-étale morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace RigEtale

/-- In a cartesian square of locally Noetherian formal algebraic spaces, the
base change of a rig-étale morphism along an adic morphism is rig-étale.
Adicness is expressed by representability by algebraic spaces. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Z W : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) [RigEtale f]
    (hg : AlgebraicSpace.representableByAlgebraicSpaces g) :
    RigEtale snd :=
  sorry

/-- The pullback projection of a rig-étale morphism of locally Noetherian
formal algebraic spaces along an adic morphism is rig-étale. Adicness is
expressed by representability by algebraic spaces. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [RigEtale f]
    (hg : AlgebraicSpace.representableByAlgebraicSpaces g)
    [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)] :
    RigEtale (pullback.snd f g) := by
  exact of_isPullback (IsPullback.of_hasPullback f g) hg

/-- The pullback projection of a rig-étale morphism of locally Noetherian
formal algebraic spaces is rig-étale when representability of the base-change
morphism by algebraic spaces is available as a fact. -/
instance instPullbackSnd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [RigEtale f]
    [Fact (AlgebraicSpace.representableByAlgebraicSpaces g)]
    [IsFormalAlgebraicSpace (pullback f g)]
    [IsLocallyNoetherian (pullback f g)] :
    RigEtale (pullback.snd f g) := by
  exact pullback_snd f g Fact.out

end RigEtale

end AlgebraicGeometry.FormalAlgebraicSpace
