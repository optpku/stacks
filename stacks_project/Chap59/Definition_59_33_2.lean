/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocalRing
public import ReasLib.AlgebraicGeometry.Scheme.Henselization
import StacksCheckRecall

open AlgebraicGeometry

universe u v

@[expose] public section

/- Definition 59.33.2 (1): the étale local ring at a geometric point is the stalk of the
structure sheaf on the small étale site, denoted `𝒪_{S, s̄}ˢʰ`. -/
@[stacks 03PS] #check
  (AlgebraicGeometry.Scheme.etaleLocalRing :
    ∀ (S : Scheme.{u}) (s : Scheme.GeometricPoint S), Type u)

/- Definition 59.33.2 (2): the henselization of the local ring at the image of a geometric point
is the canonical local-algebra notion `IsHenselizationOf`. See Algebra, Definition 10.155.3,
and Theorem 59.32.8. Notation: `𝒪_{S, s}ʰ`. -/
@[stacks 03PS] #check
  (IsHenselizationOf :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] (Rh : Type v) [CommRing Rh]
      [Algebra R Rh], Prop)

/- Definition 59.33.2 (3): the strict henselization of `S` at a geometric point is the
scheme `Spec` of the étale local ring at that geometric point. -/
@[stacks 03PS] #check
  (AlgebraicGeometry.Scheme.strictHenselizationAt :
    ∀ (S : Scheme.{u}) (s : Scheme.GeometricPoint S), Scheme.{u})

/- Definition 59.33.2 (4): the henselization of `S` at a point is the scheme `Spec` of a
chosen henselization of the Zariski local ring. -/
@[stacks 03PS] #check
  (AlgebraicGeometry.Scheme.henselizationScheme :
    ∀ (S : Scheme.{u}) (x : S) (Rh : Type v) [CommRing Rh]
      [Algebra (S.presheaf.stalk x) Rh]
      [IsHenselizationOf (S.presheaf.stalk x) Rh], Scheme.{v})
