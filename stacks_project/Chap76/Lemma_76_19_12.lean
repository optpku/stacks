module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth.Differentials.Transitivity
import StacksCheckRecall

/-!
# Short exactness of the transitivity sequence under formal smoothness

If `f : X ⟶ Y` is a formally smooth morphism of algebraic spaces, the canonical
transitivity sequence of relative differentials is short exact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.19.12: Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of algebraic spaces over `S`. Assume `f` is formally smooth. Then
the canonical transitivity sequence `0 ⟶ f^* Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶ Ω_{X/Y} ⟶ 0`
of Lemma 76.7.8 is short exact. Here `f^* Ω_{Y/Z}` is
`(Modules.pullback f).obj (relativeDifferentials g)`, `Ω_{X/Z}` is
`relativeDifferentials (f ≫ g)`, and `Ω_{X/Y}` is `relativeDifferentials f`. -/
@[stacks 06BI] #check
  (AlgebraicGeometry.AlgebraicSpace.FormallySmooth.relativeDifferentialsTransitivity_shortExact :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.AlgebraicSpace.FormallySmooth f],
      (AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.Transitivity.complex f g).ShortExact)
