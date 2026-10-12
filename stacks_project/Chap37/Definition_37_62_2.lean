/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Koszul
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 37.62.2 (1): a scheme morphism is Koszul at a point when it is of finite type
there and locally factors as a Koszul-regular immersion followed by a smooth morphism. -/
@[stacks 069F] #check (AlgebraicGeometry.Scheme.Hom.KoszulAt :
  {X S : AlgebraicGeometry.Scheme.{u}} → (X ⟶ S) → X → Prop)

/- Definition 37.62.2 (2): a Koszul, or local complete intersection, morphism is Koszul at
every point of its source. -/
@[stacks 069F] #check
  (AlgebraicGeometry.LocallyOfType.isLocalCompleteIntersection_iff_forall_koszulAt :
    {X S : AlgebraicGeometry.Scheme.{u}} → (f : X ⟶ S) →
      (AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f ↔
        ∀ x : X, AlgebraicGeometry.Scheme.Hom.KoszulAt f x))
