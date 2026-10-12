/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow.Derived
public import stacks_project.Chap36.Lemma_36_10_1_PseudoCoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 37.69.2 (Derived Chow's lemma): locally at any point, a separated scheme of finite
presentation over a ring admits a closed subscheme of a relative projective-space product and a
pseudo-coherent supported derived object with the stated projection and restriction properties. -/
@[stacks 0CSJ] #check
  (AlgebraicGeometry.DerivedChowPresentation.exists_of_separated_finitePresentation :
    ∀ {A : Type u} [CommRing A] {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) [AlgebraicGeometry.IsSeparated f]
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation f] (x : X),
      Nonempty (AlgebraicGeometry.DerivedChowPresentation f x))
