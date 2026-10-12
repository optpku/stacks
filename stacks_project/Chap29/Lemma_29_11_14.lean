/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Artinian
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.isAffineHom_of_finite_discrete_source : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Finite X] [DiscreteTopology X], IsAffineHom f)

/- Lemma 29.11.14

Every morphism from the spectrum of an Artinian ring is affine. -/
@[stacks 01SI] #check (AlgebraicGeometry.isAffineHom_of_artinianSpec :
  ∀ {S : Scheme.{u}} {A : CommRingCat.{u}} [IsArtinianRing A] (f : Spec A ⟶ S), IsAffineHom f)
