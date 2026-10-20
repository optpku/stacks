module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.BaseChange

/-!
# Base change of quasi-compact morphisms of algebraic spaces

Quasi-compact morphisms of algebraic spaces are stable under arbitrary base change.
This module records the morphism-level pullback companions for the existing
`QuasiCompact` class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check
  (QuasiCompact.of_isPullback :
    ∀ {S : Scheme.{u}} {X Y Y' B : AlgebraicSpace S}
      {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y} {g' : Y' ⟶ X},
      IsPullback f' g' g f → QuasiCompact g → QuasiCompact g')

#check
  (QuasiCompact.pullback_snd :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y},
      QuasiCompact f → (g : Z ⟶ Y) → [HasPullback f g] →
        QuasiCompact (pullback.snd f g))

#check
  (quasiCompact_pullback_snd :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiCompact f] [HasPullback f g],
      QuasiCompact (pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
