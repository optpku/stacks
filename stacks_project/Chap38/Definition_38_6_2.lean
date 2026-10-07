module

public import ReasLib.Algebra.Module.Devissage.Complete
import StacksCheckRecall

universe u

/- Definition 38.6.2: `Module.Devissage.Complete` records a complete dévissage of a finite
`S`-module over a prime of `R`. -/
@[stacks 05HX] #check (Module.Devissage.Complete :
  (R : Type u) → [CommRing R] → (S : FGAlgCat.{u} R) →
    FGModuleCat.{u} S.obj → PrimeSpectrum R → Type (u + 1))
