module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.EtaleComparison
import StacksCheckRecall

/-!
# Lemma 84.6.4

The printed formula for `a_Y` has an `X` subscript typo; the well-typed
composite uses `π_Y ∘ ε_Y` on the `Y` side.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Fppf
open scoped MorphismOfTopoiIn

universe u

/- Lemma 84.6.4 (1): the big fppf and big étale morphisms commute with
identity-induced comparison. -/
@[stacks 0DGI] #check (AlgebraicGeometry.AlgebraicSpace.Fppf.bigEtaleCommSq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Nonempty (CatCommSq
      (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1}
        (fppfTopology S) f).pushforward
      (epsilon X).pushforward
      (epsilon Y).pushforward
      (Etale.Big.morphismOfTopoi f).pushforward))

/- Lemma 84.6.4 (2): the big fppf and small étale morphisms commute with
the comparisons `a_X = π_X ∘ ε_X` and `a_Y = π_Y ∘ ε_Y`. -/
@[stacks 0DGI] #check (AlgebraicGeometry.AlgebraicSpace.Fppf.smallEtaleCommSq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Nonempty (CatCommSq
      (CategoryTheory.Over.Site.morphismOfTopoi.{u + 1, u + 1, u + 1}
        (fppfTopology S) f).pushforward
      (Etale.SmallToBig.fppfComparison X).pushforward
      (Etale.SmallToBig.fppfComparison Y).pushforward
      (smallEtaleMorphismOfTopoi f).pushforward))
