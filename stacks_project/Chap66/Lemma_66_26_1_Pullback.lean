module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.EtalePullback

/-! The canonical public owner supplies étale module pullback and exactness. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.pullback_exact :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      exactFunctor Y.Modules X.Modules (Modules.pullback f))
