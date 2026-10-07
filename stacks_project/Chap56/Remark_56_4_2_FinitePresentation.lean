module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation.Monoidal

@[expose] public section

universe uR uM

/- Finitely presented modules inherit the tensor-product monoidal structure. -/
#check (ModuleCat.isFinitePresentation.instIsMonoidal :
  ∀ (R : Type uR) [CommRing R],
    (ModuleCat.isFinitePresentation.{uR, max uR uM} R).IsMonoidal)
