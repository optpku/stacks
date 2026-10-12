/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyOpen.FinitePresentation
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 37.74.1 (1): a morphism of schemes is universally open if and only if its base
change along every locally finitely presented morphism is an open map. -/
@[stacks 0F31] #check
  (AlgebraicGeometry.UniversallyOpen.iff_isOpenMap_baseChange_of_locallyOfFinitePresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S), UniversallyOpen f ↔
      ∀ ⦃S' : Scheme.{u}⦄ (g : S' ⟶ S), LocallyOfFinitePresentation g →
        IsOpenMap (pullback.snd f g).base)

/- Lemma 37.74.1 (2): a morphism of schemes is universally open if and only if its base
change along every finite-dimensional relative affine-space projection is an open map. -/
@[stacks 0F31] #check
  (AlgebraicGeometry.UniversallyOpen.iff_isOpenMap_affineSpace_baseChange :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S), UniversallyOpen f ↔
      ∀ n : ℕ,
        IsOpenMap (pullback.snd f (AffineSpace (ULift.{u} (Fin n)) S ↘ S)).base)
