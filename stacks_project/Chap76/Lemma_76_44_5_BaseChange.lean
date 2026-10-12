/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Lemma_76_44_3_RegularImmersion

/-!
# Flat base change of regular immersions of algebraic spaces

Koszul-regular, `H₁`-regular, and quasi-regular immersions of algebraic
spaces are preserved by base change along a flat morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion

/-- Koszul-regular immersions of algebraic spaces are stable under base change
along a flat morphism. -/
instance instIsStableUnderBaseChangeAgainst {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChangeAgainst
      (@IsKoszulRegularImmersion S : MorphismProperty (AlgebraicSpace S))
      (@Flat S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- Koszul-regular immersions of algebraic spaces are stable under base change
along a fixed flat morphism. -/
instance instIsStableUnderBaseChangeAlong {S : Scheme.{u}}
    {X' X : AlgebraicSpace S} (f : X' ⟶ X) [Flat f] :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsKoszulRegularImmersion S : MorphismProperty (AlgebraicSpace S)) f :=
  sorry

/-- The pullback of a Koszul-regular immersion of algebraic spaces along a
flat morphism, expressed by an `IsPullback` square, is a Koszul-regular
immersion. -/
theorem of_isPullback {S : Scheme.{u}} {Z X Z' X' : AlgebraicSpace S}
    {i : Z ⟶ X} {f : X' ⟶ X} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} [Flat f]
    (sq : IsPullback g i' i f) [IsKoszulRegularImmersion i] :
    IsKoszulRegularImmersion i' :=
  sorry

/-- The base-change projection `pullback.snd i f` of a Koszul-regular immersion
`i : Z ⟶ X` along a flat morphism `f` is a Koszul-regular immersion. -/
instance pullback_snd {S : Scheme.{u}} {Z X X' : AlgebraicSpace S}
    (i : Z ⟶ X) (f : X' ⟶ X) [HasPullback i f] [IsKoszulRegularImmersion i]
    [Flat f] : IsKoszulRegularImmersion (pullback.snd i f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion

namespace AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion

/-- `H₁`-regular immersions of algebraic spaces are stable under base change
along a flat morphism. -/
instance instIsStableUnderBaseChangeAgainst {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChangeAgainst
      (@IsH1RegularImmersion S : MorphismProperty (AlgebraicSpace S))
      (@Flat S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- `H₁`-regular immersions of algebraic spaces are stable under base change
along a fixed flat morphism. -/
instance instIsStableUnderBaseChangeAlong {S : Scheme.{u}}
    {X' X : AlgebraicSpace S} (f : X' ⟶ X) [Flat f] :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsH1RegularImmersion S : MorphismProperty (AlgebraicSpace S)) f :=
  sorry

/-- The pullback of an `H₁`-regular immersion of algebraic spaces along a
flat morphism, expressed by an `IsPullback` square, is an `H₁`-regular
immersion. -/
theorem of_isPullback {S : Scheme.{u}} {Z X Z' X' : AlgebraicSpace S}
    {i : Z ⟶ X} {f : X' ⟶ X} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} [Flat f]
    (sq : IsPullback g i' i f) [IsH1RegularImmersion i] :
    IsH1RegularImmersion i' :=
  sorry

/-- The base-change projection `pullback.snd i f` of an `H₁`-regular immersion
`i : Z ⟶ X` along a flat morphism `f` is an `H₁`-regular immersion. -/
instance pullback_snd {S : Scheme.{u}} {Z X X' : AlgebraicSpace S}
    (i : Z ⟶ X) (f : X' ⟶ X) [HasPullback i f] [IsH1RegularImmersion i]
    [Flat f] : IsH1RegularImmersion (pullback.snd i f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion

namespace AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion

/-- Quasi-regular immersions of algebraic spaces are stable under base change
along a flat morphism. -/
instance instIsStableUnderBaseChangeAgainst {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChangeAgainst
      (@IsQuasiRegularImmersion S : MorphismProperty (AlgebraicSpace S))
      (@Flat S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- Quasi-regular immersions of algebraic spaces are stable under base change
along a fixed flat morphism. -/
instance instIsStableUnderBaseChangeAlong {S : Scheme.{u}}
    {X' X : AlgebraicSpace S} (f : X' ⟶ X) [Flat f] :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsQuasiRegularImmersion S : MorphismProperty (AlgebraicSpace S)) f :=
  sorry

/-- The pullback of a quasi-regular immersion of algebraic spaces along a
flat morphism, expressed by an `IsPullback` square, is a quasi-regular
immersion. -/
theorem of_isPullback {S : Scheme.{u}} {Z X Z' X' : AlgebraicSpace S}
    {i : Z ⟶ X} {f : X' ⟶ X} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} [Flat f]
    (sq : IsPullback g i' i f) [IsQuasiRegularImmersion i] :
    IsQuasiRegularImmersion i' :=
  sorry

/-- The base-change projection `pullback.snd i f` of a quasi-regular immersion
`i : Z ⟶ X` along a flat morphism `f` is a quasi-regular immersion. -/
instance pullback_snd {S : Scheme.{u}} {Z X X' : AlgebraicSpace S}
    (i : Z ⟶ X) (f : X' ⟶ X) [HasPullback i f] [IsQuasiRegularImmersion i]
    [Flat f] : IsQuasiRegularImmersion (pullback.snd i f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion
