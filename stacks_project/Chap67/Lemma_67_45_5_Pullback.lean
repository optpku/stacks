/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.BaseChange

/-!
Typed compatibility checks for pullback stability of integral and finite
morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.isIntegralHom_of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → IsIntegralHom g → IsIntegralHom g')

#check (AlgebraicGeometry.AlgebraicSpace.IsIntegralHom.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    IsIntegralHom f → (g : Z ⟶ Y) → [HasPullback f g] →
      IsIntegralHom (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.isIntegralHom_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y),
    [IsIntegralHom f] → [HasPullback f g] →
      IsIntegralHom (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.isFinite_of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
    {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
    IsPullback f' g' g f → IsFinite g → IsFinite g')

#check (AlgebraicGeometry.AlgebraicSpace.IsFinite.pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
    IsFinite f → (g : Z ⟶ Y) → [HasPullback f g] →
      IsFinite (pullback.snd f g))

#check (AlgebraicGeometry.AlgebraicSpace.isFinite_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y),
    [IsFinite f] → [HasPullback f g] →
      IsFinite (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
