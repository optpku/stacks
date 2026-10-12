/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Descent

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Descent of a scheme-morphism property along surjective morphisms satisfying `Q`
whose source and target are affine. -/
class AffineDescendsAlong (P Q : MorphismProperty Scheme.{u}) : Prop where
  /-- Apply affine descent to a pullback square over affine source and target schemes. -/
  of_isPullback {A S' X S : Scheme.{u}} [IsAffine S'] [IsAffine S]
    {fst : A ⟶ S'} {snd : A ⟶ X} {p : S' ⟶ S} {f : X ⟶ S} :
    IsPullback fst snd p f → Surjective p → Q p → P fst → P f

namespace AffineDescendsAlong

variable (P Q : MorphismProperty Scheme.{u})

/-- Unrestricted descent along surjective `Q`-morphisms implies affine descent. -/
instance ofDescendsAlong
    [P.DescendsAlong ((@Surjective : MorphismProperty Scheme.{u}) ⊓ Q)] :
    AffineDescendsAlong P Q := sorry

/-- Apply affine descent to the first projection of a pullback. -/
lemma of_pullback_fst {S' X S : Scheme.{u}} [IsAffine S'] [IsAffine S]
    (p : S' ⟶ S) (f : X ⟶ S) [HasPullback p f]
    (hp : Surjective p) (hQ : Q p) (hfst : P (pullback.fst p f)) : P f := sorry

end AffineDescendsAlong

end AlgebraicGeometry
