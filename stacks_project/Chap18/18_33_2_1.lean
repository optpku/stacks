module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import StacksCheckRecall

/-!
# Objectwise presentation of relative differentials

The equation is a direct specialization of the canonical Mathlib presheaf of Kähler
differentials; no second quotient construction is introduced.
-/

@[expose] public section

open CategoryTheory
open PresheafOfModules.DifferentialsConstruction

/- Equation 18.33.2.1: relative differentials are objectwise the canonical Kähler
differentials of the map on sections. -/
@[stacks 04BL "Equation (18.33.2.1)"]
#check (@relativeDifferentials'_obj)

/- The canonical kernel and quotient presentation remain available from the algebraic owner. -/
#check (@KaehlerDifferential.kerTotal_eq)
#check (@KaehlerDifferential.quotKerTotalEquiv)
