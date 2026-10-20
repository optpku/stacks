module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FinitePresentation.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 74.6.7: for a finite morphism of finite presentation `f : X ⟶ Y` of
algebraic spaces over a scheme `S`, a quasi-coherent `𝒪_X`-module `ℱ` is of
finite presentation if and only if `(pushforward f).obj ℱ` is of finite
presentation as an `𝒪_Y`-module. -/
@[stacks 0610] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isFinitePresentation_iff_pushforward_of_isFinite :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.IsFinite f]
      [AlgebraicGeometry.AlgebraicSpace.FinitePresentation f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      ℱ.IsFinitePresentation ↔
        ((AlgebraicGeometry.AlgebraicSpace.Modules.pushforward f).obj ℱ).IsFinitePresentation)
