/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Descent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 33.25.9 (1): smoothness at a point over a field descends along a morphism that is flat
at that point. -/
@[stacks 05AX] #check
  (AlgebraicGeometry.Scheme.Hom.smoothAt_of_comp_of_flatAt :
    ∀ {k : Type u} [Field k] {X Y : Scheme.{u}}
      (f : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of k))
      [LocallyOfFiniteType (f ≫ g)] [LocallyOfFiniteType g] (x : X),
      (f ≫ g).SmoothAt x → Scheme.Hom.flatAt f x → g.SmoothAt (f x))

/- Lemma 33.25.9 (2): smoothness over a field descends along a flat surjective morphism. -/
@[stacks 05AX] #check
  (AlgebraicGeometry.Scheme.Hom.smooth_of_comp_of_flat_of_surjective :
    ∀ {k : Type u} [Field k] {X Y : Scheme.{u}}
      (f : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of k))
      [LocallyOfFiniteType g] [Flat f] [Surjective f] [Smooth (f ≫ g)],
      Smooth g)
