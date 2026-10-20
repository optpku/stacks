module

public import ReasLib.Algebra.Category.ModuleCat.Monoidal.Universe
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.Algebra.Module.FinitePresentation.TensorProduct

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.ObjectProperty

universe uR uM

namespace ModuleCat

variable (R : Type uR) [CommRing R]

namespace isFinitePresentation

/-- Tensor products of finitely presented modules remain finitely presented. -/
theorem prop_tensor {M N : ModuleCat.{max uR uM} R}
    (hM : isFinitePresentation.{uR, max uR uM} R M)
    (hN : isFinitePresentation.{uR, max uR uM} R N) :
    isFinitePresentation.{uR, max uR uM} R
      (ModuleCat.of R (TensorProduct R M N)) := sorry

/-- The full subcategory of finitely presented modules is monoidal under the
usual tensor product. -/
instance instIsMonoidal :
    (isFinitePresentation.{uR, max uR uM} R).IsMonoidal := sorry

end isFinitePresentation

end ModuleCat
