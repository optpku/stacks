module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_20_2_Affine

/-!
# Affine detection and affine descent

A morphism property of algebraic spaces over a scheme `S` may be tested on
base changes along morphisms from affine schemes, and may descend along
surjective morphisms of affine schemes over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism property of algebraic spaces over a scheme `S` is affine-local on the
target if a morphism has the property if and only if every base change along a
morphism from an affine scheme over `S` has the property. -/
class AffineLocalAtTarget {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S)) :
    Prop where
  /-- Detection by base change along morphisms from affine schemes. -/
  iff_forall_affine {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔
      ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left] (g : ofOver Z ⟶ Y),
        P (pullback.snd f g)

namespace AffineLocalAtTarget

variable {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}

/-- The trivial morphism property is affine-local on the target. -/
instance instTop : AffineLocalAtTarget (⊤ : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- Affine-locality on the target implies stability under arbitrary base change. -/
instance instIsStableUnderBaseChange [AffineLocalAtTarget P] :
    P.IsStableUnderBaseChange :=
  sorry

end AffineLocalAtTarget

/-- Descent of a morphism property of algebraic spaces along surjective
morphisms satisfying `Q` whose source and target are affine schemes over `S`. -/
class AffineDescendsAlong {S : Scheme.{u}}
    (P Q : MorphismProperty (AlgebraicSpace S)) : Prop where
  /-- Apply affine descent to a pullback square over affine source and target
  schemes. -/
  of_isPullback {A X : AlgebraicSpace S} {Z' Z : Over S}
      [AlgebraicGeometry.IsAffine Z'.left] [AlgebraicGeometry.IsAffine Z.left]
      {fst : A ⟶ ofOver Z'} {snd : A ⟶ X}
      {p : ofOver Z' ⟶ ofOver Z} {f : X ⟶ ofOver Z} :
    IsPullback fst snd p f → Surjective p → Q p → P fst → P f

namespace AffineDescendsAlong

variable {S : Scheme.{u}} {P Q : MorphismProperty (AlgebraicSpace S)}

/-- Unrestricted descent along surjective `Q`-morphisms implies affine descent. -/
instance ofDescendsAlong
    [P.DescendsAlong ((@Surjective S : MorphismProperty (AlgebraicSpace S)) ⊓ Q)] :
    AffineDescendsAlong P Q :=
  sorry

/-- Apply affine descent to the first projection of a pullback along a morphism
of affine schemes over `S`. -/
theorem of_pullback_fst [AffineDescendsAlong P Q]
    {X : AlgebraicSpace S} {Z' Z : Over S}
    [AlgebraicGeometry.IsAffine Z'.left] [AlgebraicGeometry.IsAffine Z.left]
    (p : ofOver Z' ⟶ ofOver Z) (f : X ⟶ ofOver Z)
    (hp : Surjective p) (hQ : Q p) (hfst : P (pullback.fst p f)) : P f :=
  sorry

/-- Affine descent also applies when the source and target are affine algebraic
spaces. -/
theorem of_isPullback_isAffine [AffineDescendsAlong P Q]
    {A Z' X Z : AlgebraicSpace S} [IsAffine Z'] [IsAffine Z]
    {fst : A ⟶ Z'} {snd : A ⟶ X} {p : Z' ⟶ Z} {f : X ⟶ Z} :
    IsPullback fst snd p f → Surjective p → Q p → P fst → P f :=
  sorry

end AffineDescendsAlong

end AlgebraicGeometry.AlgebraicSpace
