module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FormalModification

/-!
# Base change of formal modifications
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
  CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.FormalModification

/-- In a cartesian square of locally Noetherian formal algebraic spaces, the
base change of a formal modification along an adic morphism is a formal
modification. Adicness is expressed by representability by algebraic spaces. -/
theorem of_isPullback {S : Scheme.{u}} {X Y Z W : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z] [IsFormalAlgebraicSpace W]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian Z] [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) [LocallyOfFiniteType f]
    [FormalModification f]
    (hg : AlgebraicSpace.representableByAlgebraicSpaces g)
    [LocallyOfFiniteType snd] :
    FormalModification snd :=
  sorry

/-- The pullback projection of a formal modification of locally Noetherian
formal algebraic spaces along an adic morphism is a formal modification.
Adicness is expressed by representability by algebraic spaces. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [LocallyOfFiniteType f]
    [FormalModification f]
    (hg : AlgebraicSpace.representableByAlgebraicSpaces g) :
    FormalModification (pullback.snd f g) := by
  exact of_isPullback (IsPullback.of_hasPullback f g) hg

/-- The pullback projection of a formal modification of locally Noetherian
formal algebraic spaces is a formal modification when adicness of the
base-change morphism is available as a fact. -/
instance instPullbackSnd {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [LocallyOfFiniteType f]
    [FormalModification f]
    [Fact (AlgebraicSpace.representableByAlgebraicSpaces g)] :
    FormalModification (pullback.snd f g) := by
  exact pullback_snd f g Fact.out

end AlgebraicGeometry.FormalAlgebraicSpace.FormalModification
