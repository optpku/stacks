module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 38.34.7: a surjective proper morphism of finite presentation, regarded as a
singleton family, is an h covering. -/
@[stacks 0ETW] #check
  (AlgebraicGeometry.Scheme.HCovering.singletonOfProperSurjective :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
      [Surjective f] [IsProper f] [Hom.FinitePresentation f],
      HCovering (fun _ : PUnit ↦ Over.mk f))

end AlgebraicGeometry.Scheme
