module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

variable {S T : Scheme.{u}}

/- This compatibility bridge re-exports the ringed-site morphism API from its mathematical owner. -/
#check (AlgebraicGeometry.StandardTopology.Big.pullbackProjection :
  ∀ f : T ⟶ S, Over.pullback f ⋙ Over.forget T ⟶ Over.forget S)
