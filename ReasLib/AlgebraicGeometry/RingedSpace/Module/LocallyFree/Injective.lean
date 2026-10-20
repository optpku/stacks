module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract.Injective
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FiniteFreeRetract
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite locally free tensor factors and injectives on ringed spaces

Finite locally free module sheaves are locally finite-free retracts, so the site-level duality
API makes their tensor functors preserve injective objects automatically.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace SheafOfModules.IsFiniteLocallyFree

variable {X : RingedSpace.{u}}

/-- Left tensoring by a finite locally free module sheaf on a ringed space preserves injective
objects.  This specialization lets typeclass search recover the coefficient sheaf from `X`. -/
@[stacks 01E7 "left tensor preserves injectives", instance]
instance tensorLeft_preservesInjectiveObjects
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    (tensorLeft E).PreservesInjectiveObjects := sorry

/-- Right tensoring by a finite locally free module sheaf on a ringed space preserves injective
objects.  This specialization lets typeclass search recover the coefficient sheaf from `X`. -/
@[stacks 01E7 "right tensor preserves injectives", instance]
instance tensorRight_preservesInjectiveObjects
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    (tensorRight E).PreservesInjectiveObjects := sorry

/-- Lemma 20.54.1: tensoring a finite locally free module sheaf with an injective module sheaf
gives an injective module sheaf. -/
@[stacks 01E7]
theorem tensor_injective
    (E : X.Modules) [E.IsFiniteLocallyFree] {I : X.Modules} (hI : Injective I) :
    Injective (E ⊗ I) := sorry

section Inference

variable (E : X.Modules) [E.IsFiniteLocallyFree]

#synth (tensorLeft E).PreservesInjectiveObjects
#synth (tensorRight E).PreservesInjectiveObjects

end Inference

end SheafOfModules.IsFiniteLocallyFree
